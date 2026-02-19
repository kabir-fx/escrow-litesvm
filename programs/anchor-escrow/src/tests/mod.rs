#[cfg(test)]
mod tests {
    use {
        anchor_lang::{
            prelude::msg, solana_program::{program_pack::Pack, clock::Clock}, AccountDeserialize, InstructionData,
            ToAccountMetas,
        },
        anchor_spl::{
            associated_token::{self, spl_associated_token_account},
            token::spl_token,
        },
        litesvm::LiteSVM,
        litesvm_token::{
            spl_token::ID as TOKEN_PROGRAM_ID, CreateAssociatedTokenAccount, CreateMint, MintTo,
        },
        solana_account::Account,
        solana_address::Address,
        solana_instruction::Instruction,
        solana_keypair::Keypair,
        solana_message::Message,
        solana_pubkey::Pubkey,
        solana_rpc_client::rpc_client::RpcClient,
        solana_sdk_ids::system_program::ID as SYSTEM_PROGRAM_ID,
        solana_signer::Signer,
        solana_transaction::Transaction,
        std::{path::PathBuf, str::FromStr},
    };

    static PROGRAM_ID: Pubkey = crate::ID;

    // ............................................................................
    // Test Context - holds all state needed for escrow tests
    // ............................................................................

    // Struct to store all the relevant components like keypair, pubkeys, etc all in one place for easier access accross different tests
    struct TestContext {
        program: LiteSVM,
        payer: Keypair, // acts as maker
        taker: Keypair,
        mint_a: Pubkey,
        mint_b: Pubkey,
        maker_ata_a: Pubkey,
        maker_ata_b: Pubkey,
        taker_ata_a: Pubkey,
        taker_ata_b: Pubkey,
        escrow: Pubkey,
        vault: Pubkey,
        seed: u64,
    }

    impl TestContext {
        fn maker(&self) -> Pubkey {
            self.payer.pubkey()
        }
    }

    // ............................................................................
    // Setup Functions
    // ............................................................................

    /// Initialize LiteSVM with the program loaded and funded accounts
    fn setup_litesvm() -> (LiteSVM, Keypair, Keypair) {
        let mut program = LiteSVM::new();
        let payer = Keypair::new();
        let taker = Keypair::new();

        // Load program SO file
        let so_path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/deploy/anchor_escrow.so");
        let program_data = std::fs::read(so_path).expect("Failed to read program SO file");
        program.add_program(PROGRAM_ID, &program_data);

        // Load accounts from devnet for realistic lamport amounts
        let rpc_client = RpcClient::new("https://api.devnet.solana.com");

        // Set the account for Maker/payer's account
        let payer_account_address =
            Address::from_str("BW5as1xNpMygprNnd74BNRAvhnYfseZDexWjhrAFzNEP").unwrap();
        let fetched_payer_account = rpc_client
            .get_account(&payer_account_address)
            .expect("Failed to fetch payer account from devnet");

        program
            .set_account(
                payer.pubkey(),
                Account {
                    lamports: fetched_payer_account.lamports,
                    data: fetched_payer_account.data,
                    owner: Pubkey::from(fetched_payer_account.owner.to_bytes()),
                    executable: fetched_payer_account.executable,
                    rent_epoch: fetched_payer_account.rent_epoch,
                },
            )
            .unwrap();

        // Set the account for Taker's account
        let taker_account_address =
            Address::from_str("E6Mj2AaUtNRPuuB9XoU8UrdwDyfd7PePHNLzJCSfquep").unwrap();
        let fetched_taker_account = rpc_client
            .get_account(&taker_account_address)
            .expect("Failed to fetch taker account from devnet");

        program
            .set_account(
                taker.pubkey(),
                Account {
                    lamports: fetched_taker_account.lamports,
                    data: fetched_taker_account.data,
                    owner: Pubkey::from(fetched_taker_account.owner.to_bytes()),
                    executable: fetched_taker_account.executable,
                    rent_epoch: fetched_taker_account.rent_epoch,
                },
            )
            .unwrap();

        // Return reusable components for tests
        (program, payer, taker)
    }

    /// Creates a complete escrow test context with mints, ATAs, and derived PDAs
    fn setup_escrow_context(seed: u64) -> TestContext {
        let (mut program, payer, taker) = setup_litesvm();
        let maker = payer.pubkey();

        // Create mints
        let mint_a = CreateMint::new(&mut program, &payer)
            .decimals(6)
            .authority(&maker)
            .send()
            .unwrap();

        let mint_b = CreateMint::new(&mut program, &taker)
            .decimals(6)
            .authority(&taker.pubkey())
            .send()
            .unwrap();

        // Create maker's ATAs
        let maker_ata_a = CreateAssociatedTokenAccount::new(&mut program, &payer, &mint_a)
            .owner(&maker)
            .send()
            .unwrap();
        let maker_ata_b = CreateAssociatedTokenAccount::new(&mut program, &payer, &mint_b)
            .owner(&maker)
            .send()
            .unwrap();

        // Create taker's ATAs
        let taker_ata_a = CreateAssociatedTokenAccount::new(&mut program, &taker, &mint_a)
            .owner(&taker.pubkey())
            .send()
            .unwrap();
        let taker_ata_b = CreateAssociatedTokenAccount::new(&mut program, &taker, &mint_b)
            .owner(&taker.pubkey())
            .send()
            .unwrap();

        // Derive escrow PDA
        let escrow = Pubkey::find_program_address(
            &[b"escrow", maker.as_ref(), &seed.to_le_bytes()],
            &PROGRAM_ID,
        )
        .0;

        // Derive vault ATA (owned by escrow PDA)
        let vault = associated_token::get_associated_token_address(&escrow, &mint_a);

        // Mint tokens to maker and taker
        MintTo::new(&mut program, &payer, &mint_a, &maker_ata_a, 1_000_000_000)
            .send()
            .unwrap();
        MintTo::new(&mut program, &taker, &mint_b, &taker_ata_b, 1_000_000_000)
            .send()
            .unwrap();

        TestContext {
            program,
            payer,
            taker,
            mint_a,
            mint_b,
            maker_ata_a,
            maker_ata_b,
            taker_ata_a,
            taker_ata_b,
            escrow,
            vault,
            seed,
        }
    }

    // ............................................................................
    // Instruction Builders
    // ............................................................................

    fn build_make_instruction(ctx: &TestContext, deposit: u64, receive: u64) -> Instruction {
        Instruction {
            program_id: PROGRAM_ID,
            accounts: crate::accounts::Make {
                maker: ctx.maker(),
                mint_a: ctx.mint_a,
                mint_b: ctx.mint_b,
                maker_ata_a: ctx.maker_ata_a,
                escrow: ctx.escrow,
                vault: ctx.vault,
                associated_token_program: spl_associated_token_account::ID,
                token_program: TOKEN_PROGRAM_ID,
                system_program: SYSTEM_PROGRAM_ID,
            }
            .to_account_metas(None),
            data: crate::instruction::Make {
                deposit,
                seed: ctx.seed,
                receive,
            }
            .data(),
        }
    }

    fn build_take_instruction(ctx: &TestContext) -> Instruction {
        Instruction {
            program_id: PROGRAM_ID,
            accounts: crate::accounts::Take {
                taker: ctx.taker.pubkey(),
                maker: ctx.maker(),
                mint_a: ctx.mint_a,
                mint_b: ctx.mint_b,
                taker_ata_a: ctx.taker_ata_a,
                taker_ata_b: ctx.taker_ata_b,
                maker_ata_b: ctx.maker_ata_b,
                escrow: ctx.escrow,
                vault: ctx.vault,
                associated_token_program: spl_associated_token_account::ID,
                token_program: TOKEN_PROGRAM_ID,
                system_program: SYSTEM_PROGRAM_ID,
            }
            .to_account_metas(None),
            data: crate::instruction::Take {}.data(),
        }
    }

    fn build_refund_instruction(ctx: &TestContext) -> Instruction {
        Instruction {
            program_id: PROGRAM_ID,
            accounts: crate::accounts::Refund {
                maker: ctx.maker(),
                mint_a: ctx.mint_a,
                maker_ata_a: ctx.maker_ata_a,
                escrow: ctx.escrow,
                vault: ctx.vault,
                token_program: TOKEN_PROGRAM_ID,
                system_program: SYSTEM_PROGRAM_ID,
            }
            .to_account_metas(None),
            data: crate::instruction::Refund {}.data(),
        }
    }

    // ............................................................................
    // Assertion Helpers
    // ............................................................................

    /// Assert that an account has been closed (0 lamports or removed)
    fn assert_account_closed(program: &LiteSVM, account: &Pubkey, name: &str) {
        match program.get_account(account) {
            Some(a) if a.lamports == 0 => msg!("{} closed successfully (0 lamports)", name),
            Some(a) => panic!("{} should be closed but has {} lamports", name, a.lamports),
            None => msg!("{} closed successfully (removed)", name),
        }
    }

    /// Assert escrow state matches expected values
    fn assert_escrow_state(
        program: &LiteSVM,
        escrow: &Pubkey,
        expected_seed: u64,
        expected_maker: &Pubkey,
        expected_mint_a: &Pubkey,
        expected_mint_b: &Pubkey,
        expected_receive: u64,
    ) {
        let escrow_account = program
            .get_account(escrow)
            .expect("Escrow account should exist");
        let escrow_data = crate::state::Escrow::try_deserialize(&mut escrow_account.data.as_ref())
            .expect("Failed to deserialize escrow");

        assert_eq!(escrow_data.seed, expected_seed, "Seed mismatch");
        assert_eq!(escrow_data.maker, *expected_maker, "Maker mismatch");
        assert_eq!(escrow_data.mint_a, *expected_mint_a, "Mint A mismatch");
        assert_eq!(escrow_data.mint_b, *expected_mint_b, "Mint B mismatch");
        assert_eq!(
            escrow_data.receive, expected_receive,
            "Receive amount mismatch"
        );
    }

    /// Assert vault state matches expected values
    fn assert_vault_state(
        program: &LiteSVM,
        vault: &Pubkey,
        expected_amount: u64,
        expected_owner: &Pubkey,
        expected_mint: &Pubkey,
    ) {
        let vault_account = program
            .get_account(vault)
            .expect("Vault account should exist");
        let vault_data = spl_token::state::Account::unpack(&vault_account.data)
            .expect("Failed to unpack vault token account");

        assert_eq!(vault_data.amount, expected_amount, "Vault amount mismatch");
        assert_eq!(vault_data.owner, *expected_owner, "Vault owner mismatch");
        assert_eq!(vault_data.mint, *expected_mint, "Vault mint mismatch");
    }

    // ............................................................................
    // Tests
    // ............................................................................

    #[test]
    fn test_make() {
        // Holds all the components required for this test
        let mut ctx = setup_escrow_context(123);
        // The amount of Token A the Maker is locking inside the vault.
        let deposit = 10u64;
        // The amount of Token B the Maker wants in exchange
        let receive = 10u64;

        // Execute Make instruction
        let make_ix = build_make_instruction(&ctx, deposit, receive);
        let message = Message::new(&[make_ix], Some(&ctx.payer.pubkey()));
        let transaction = Transaction::new(&[&ctx.payer], message, ctx.program.latest_blockhash());
        let tx = ctx.program.send_transaction(transaction).unwrap();

        msg!("\n\nMake transaction successful");
        msg!("CUs Consumed: {}", tx.compute_units_consumed);

        // Assert vault state
        assert_vault_state(&ctx.program, &ctx.vault, deposit, &ctx.escrow, &ctx.mint_a);

        // Assert escrow state
        assert_escrow_state(
            &ctx.program,
            &ctx.escrow,
            ctx.seed,
            &ctx.maker(),
            &ctx.mint_a,
            &ctx.mint_b,
            receive,
        );

        msg!("test_make passed!");
    }

    #[test]
    fn test_make_and_take() {
        let mut ctx = setup_escrow_context(456);
        let deposit = 100u64;
        let receive = 50u64;

        // Step 1: Execute Make instruction
        let make_ix = build_make_instruction(&ctx, deposit, receive);
        let message = Message::new(&[make_ix], Some(&ctx.payer.pubkey()));
        let transaction = Transaction::new(&[&ctx.payer], message, ctx.program.latest_blockhash());
        ctx.program.send_transaction(transaction).unwrap();
        msg!("Make completed");

        // Push the time forward for take to pass
        let seconds_5_days = (5 * 24 * 60 * 60)+1;
        let mut clock = ctx.program.get_sysvar::<Clock>();
        
        clock.unix_timestamp += seconds_5_days; 
        
        ctx.program.set_sysvar::<Clock>(&clock);
        
        // Step 2: Execute Take instruction
        let take_ix = build_take_instruction(&ctx);
        let message = Message::new(&[take_ix], Some(&ctx.taker.pubkey()));
        let transaction = Transaction::new(&[&ctx.taker], message, ctx.program.latest_blockhash());
        let tx = ctx.program.send_transaction(transaction).unwrap();

        msg!("\n\nTake transaction successful");
        msg!("CUs Consumed: {}", tx.compute_units_consumed);

        // Assert vault is closed
        assert_account_closed(&ctx.program, &ctx.vault, "Vault");

        // Assert escrow is closed
        assert_account_closed(&ctx.program, &ctx.escrow, "Escrow");

        msg!("test_make_and_take passed!");
    }

    #[test]
    fn test_make_and_refund() {
        // Using different seeds for each test ensures that we generate a unique Escrow address for all of them.
        let mut ctx = setup_escrow_context(789);
        let deposit = 200u64;
        let receive = 100u64;

        // Step 1: Execute Make instruction
        let make_ix = build_make_instruction(&ctx, deposit, receive);
        let message = Message::new(&[make_ix], Some(&ctx.payer.pubkey()));
        let transaction = Transaction::new(&[&ctx.payer], message, ctx.program.latest_blockhash());
        ctx.program.send_transaction(transaction).unwrap();
        msg!("Make completed");

        // Step 2: Execute Refund instruction (maker cancels the escrow)
        let refund_ix = build_refund_instruction(&ctx);
        let message = Message::new(&[refund_ix], Some(&ctx.maker()));
        let transaction = Transaction::new(&[&ctx.payer], message, ctx.program.latest_blockhash());
        let tx = ctx.program.send_transaction(transaction).unwrap();

        msg!("\n\nRefund transaction successful");
        msg!("CUs Consumed: {}", tx.compute_units_consumed);

        // Assert vault is closed
        assert_account_closed(&ctx.program, &ctx.vault, "Vault");

        // Assert escrow is closed
        assert_account_closed(&ctx.program, &ctx.escrow, "Escrow");

        msg!("test_make_and_refund passed!");
    }
}
