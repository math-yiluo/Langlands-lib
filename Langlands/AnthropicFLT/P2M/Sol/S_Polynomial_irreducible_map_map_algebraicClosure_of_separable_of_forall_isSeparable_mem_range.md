# `Langlands.AnthropicFLT.P2M.Sol.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range`. Statement. `Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range`: let `K ⊆ L` be fields
with `K` separably closed in `L`, `x ∈ Lᵈ` algebraically independent over `K`, and `F ∈ K[x][Y]` monic, irreducible and
separable over `K(x)` with `F(x, y) = 0` for some `y ∈ L`. Then `F` stays irreducible over the algebraic closure of
`K`.

Proof. Stage A: `K(x)[Y]/(F)` embeds in `L` via `Y ↦ y` (`H`, `mkH`, `liftH`, `jH_injective`), so it is a field inside
`L`. Stage B: base change to the algebraic closure `K̄`: `K̄ ⊗_K K(x)[Y]/(F)` is reduced (separability, `separable_Fb`,
`isReduced_Qb`) and its nilradical is prime by the ported
`Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range` (as `K` is separably closed in
`L`; `nilradical_Qb_isPrime`), so it is a domain. Stages C, D: this ring is `K̄(x)[Y]/(F)` (`Θ`, `Λ`, `Φ_injective`), so `F`
is irreducible over `K̄(x)`, hence over `K̄[x]` being monic (`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.dvd_of_eval₂_eq_zero`
- abbrev `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Kb`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.H`
- scoped instance `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.instCommRingH`
- scoped instance `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.instAlgebraH`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.mkH`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.mkH_surjective`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.mkH_eq_zero_iff`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.mkH_self`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.liftH`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.liftH_mkH`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Fb`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Qb`
- scoped instance `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.instCommRingQb`
- scoped instance `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.instAlgebraQb`
- scoped instance `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.instAlgebraQbK`
- scoped instance `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.instIsScalarTowerQb`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.mkQ`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.mkQ_surjective`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.mkQ_eq_zero_iff`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.liftQ`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.liftQ_mkQ`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.evalXY`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.evalXY_apply`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.jH`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.jH_mkH`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.jH_injective`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.θP`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Θ₀`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.θP_map`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Θ₀_map`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Θ₀_Fb`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Θ`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.lam₁`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.lam₁_mkH`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Λ`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Λ_tmul`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.algebraMap_Qb`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Λ_Θ`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Θ_injective`
- def `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Φ`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Φ_injective`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.nilradical_Qb_isPrime`
- abbrev `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.Mb`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.separable_Fb`
- lemma `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.isReduced_Qb`
- theorem `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.P2mAbsIrred.main`
- theorem `P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range` (same contribution).
Other imports: `Mathlib`.
