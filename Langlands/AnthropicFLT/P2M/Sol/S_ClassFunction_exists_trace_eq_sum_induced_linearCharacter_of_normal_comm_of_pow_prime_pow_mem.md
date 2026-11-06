# `Langlands.AnthropicFLT.P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem`

Ported by Worker 84 for the exact-target proof of
`Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement` (Brauer's induction theorem, an input of
Henniart's 2000 proof; program `34b81620-20d7-4059-9b08-6bedd1c1c029`). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

Below, `…` abbreviates `P2MW.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem`.

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped, and its two commands used here are replaced by standard Lean:
  - FLT declares `private def _root_.MonomialProof.val (e : Entry K)` and then `p2m_export "MonomialProof" "val"`, which adds the alias `….MonomialProof.val` for that private constant. The port declares `private def val (e : Entry K)` directly inside `namespace ….MonomialProof`, so the same name `….MonomialProof.val` refers to the same definition (body unchanged), and the `p2m_export` line is removed.
  - The two commands `p2m_reactivate "….MonomialProof"` (re-activating that namespace's scoped declarations: the instance `weightAction` and the `scoped simp` lemmas `act_apply`, `weightHom_apply`) are replaced by `open scoped _root_.….MonomialProof` at the same two places (after `end MonomialProof`, and at the end of the file).
- In `extChar_lift`, after `obtain ⟨z, hz, rfl⟩ := hg`, the FLT step `simp only [Subgroup.coe_subtype]` is replaced by `change extChar (lift H e).1 (lift H e).2 (z : K) = if hg' : (z : K) ∈ H then extChar e.1 e.2 ⟨(z : K), hg'⟩ else 0`, which states the goal with the dependent conditional explicit; and `dsimp only [lift] at hmem ⊢` is inserted before `rw [MulEquiv.apply_symm_apply]`. This is the audit's compatibility edit 3, needed for the proof to check on the pinned Mathlib. The statement of `extChar_lift` is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `….solution` proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem`;
it is `MonomialProof.main`. All groups and carriers live in `Type`.

Proof (namespace `….MonomialProof`):

- Bookkeeping. `extChar L ψ` extends a unit character `ψ` of `L` by zero; an `Entry K` is a pair of a subgroup and a unit character on it; `val e` is `ClassFunction.induced e.1 (extChar e.1 e.2)`; `lsum l` sums `val` over a list of entries (`lsum_nil`, `lsum_cons`, `lsum_append`, `lsum_replicate`, `lsum_flatten_replicate`). `lift H e` transports an entry of a subgroup `H` to `K`, and `val_lift` / `induced_lsum_eq` show that inducing from `H` the extension by zero of `lsum l` equals `lsum (l.map (lift H))` (induction in stages, `ClassFunction.induced_induced`).
- Representations (`σ : Representation ℂ K W`, `W` finite-dimensional). Each `σ k` is semisimple (`isSemisimple`, from `X ^ |K| - 1`). For a subgroup `A` whose image commutes, the weight spaces `wt σ A χ = ⨅ a, maxGenEigenspace (σ a) (χ a)` give an internal direct sum of `W` (`isInternal_wt`) with finitely many nonzero summands (`finite_wt`). A nonzero weight is a character (`weight_mul`, `weight_one`, `weight_ne_zero`, `weightHom`). For normal `A`, `K` acts on weights by conjugation (scoped instance `weightAction`), `σ k` maps `wt σ A χ` isomorphically onto `wt σ A (k • χ)` (`mapsTo_smul`, `map_wt_eq`, `wtEquiv`), and the stabilizer of `χ` acts on `wt σ A χ` (`stabRep`).
- `trace_eq_sum_fixed`: if `f` permutes the summands of an internal direct sum by `π`, the trace of `f` is the sum of the traces of its restrictions to the summands fixed by `π`.
- `exists_normal_comm_not_central`: if `K / A` is a `p`-group, `A` is normal with commuting image under `f : K →* Γ`, and the image of `f` is not commutative, then some normal subgroup `B ≥ A` has commuting image and an element whose image is not central.
- `Monomial K W σ` says that the trace of `σ` is `lsum l` for some list `l`. The main step `engine` proves `Monomial K W σ` by induction on `|K| + dim W` for every `K` with a normal commutative `A` and `p`-group quotient. If `dim W = 0` the list is empty (`monomial_of_finrank_zero`). If the image of `σ` is commutative, the weight spaces of `⊤` give the trace as a sum of linear characters with multiplicities (`monomial_of_comm`, using `induced_top_of_conj_invariant`). Otherwise take `B` from `exists_normal_comm_not_central`; there are at least two weights. If `K` permutes the weights transitively, the stabilizer `H₁` of a weight `χ₁` is proper, the induction hypothesis applies to `stabRep` on `wt σ B χ₁` (with the normal commutative subgroup `A.subgroupOf H₁` of `H₁`), and the trace of `σ` is induced from `H₁` (`monomial_of_transitive`, via `trace_eq_sum_fixed`). If not, the sum `P₁` of the weight spaces in the orbit of `χ₁` and the sum `P₂` of the others are complementary nonzero `K`-stable subspaces, and the induction hypothesis applies to both (`monomial_of_isCompl`).
- `main` applies `engine` to `repOfGL ρ` (the matrix representation on `Fin n → ℂ`, `trace_repOfGL`) and converts the list into a `Fin k`-indexed family.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`; all of the following except `solution` are in `….MonomialProof`.

- Bookkeeping: def `extChar`, abbrev `Entry`, private def `val`, def `lsum`, theorems `lsum_nil`, `lsum_cons`, `lsum_append`, `lsum_replicate`, `lsum_flatten_replicate`, def `lift`, theorems `lift_snd_apply`, `extChar_lift`, `val_lift`, `induced_lsum_eq`
- Representations: theorems `isSemisimple`, `maxGenEigenspace_eq`, def `act`, theorems `act_apply` (scoped simp), `act_symm_apply`, `trace_conj`, def `wt`, theorems `mem_wt`, `isInternal_wt`, `mapsTo_wt_of_comm`, `finite_wt`, `exists_ne_zero_of_ne_bot`, `weight_mul`, `weight_one`, `weight_ne_zero`, def `weightHom`, theorem `weightHom_apply` (scoped simp), scoped instance `weightAction`, theorems `smul_weight_apply`, `mapsTo_smul`, `map_wt_eq`, def `wtEquiv`, theorems `wtEquiv_apply`, `wtEquiv_symm_apply`, `wt_smul_ne_bot_iff`, `trace_restrict_conj`, `mapsTo_of_smul_eq`, def `stabRep`, theorem `stabRep_apply`
- Trace: theorems `mapsTo_of_eq`, `trace_eq_sum_fixed`
- Group lemma: theorem `exists_normal_comm_not_central`
- Induction: def `Monomial`, theorems `monomial_of_finrank_zero`, `monomial_of_comm`, `monomial_of_isCompl`, `monomial_of_transitive`, `engine`
- Final: def `repOfGL`, theorems `repOfGL_apply`, `trace_repOfGL`, `main`
- theorem `….solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced` (same contribution).
Other imports: `Mathlib`.
