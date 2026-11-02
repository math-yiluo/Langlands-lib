# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 4 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete`. Statement. `AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isAdicComplete`: let `A` be a complete noetherian local
ring and `p : X ⟶ Spec A` proper and flat. If the closed fibre has `Γ = A/𝔪` (the map on global sections of the
base change to `A/𝔪` is bijective), then `A → Γ(X, ⊤)` is bijective.

Proof. With `X_n = X ×_A A/𝔪ⁿ` (`quot`, `XI`, `ι`, `pI`), the maps `A/𝔪ⁿ → Γ(X_n)` are bijective for all `n`, by
induction on `n` using flatness (the kernel of `Γ(X_{n+1}) → Γ(X_n)` is `𝔪ⁿ/𝔪ⁿ⁺¹ ⊗ Γ(X_0)`) and the lifting
data `LiftsAt`, `τ`, `ρ`, `LocData`, `StepHyp` (`levels_bijective`). Global sections of the proper `X` form a
finite `A`-module, and by the theorem on formal functions (here proved directly: a section vanishing on all
`X_n` is zero, `eq_zero_of_forall_ι_appTop_eq_zero`) the map `Γ(X) → lim Γ(X_n) = A` is injective, which with
completeness of `A` gives bijectivity (`bijective_alg_top`, `bijective_appTop`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T1.mem_map_colon_of_flat`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T1.ker_eq_map_and_surjective_of_isPushout`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.quot`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.XI`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.ι`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.pI`
- private def `SolH0T2.alg`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.φ`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.alg_map`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.appLE_top_top`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.appLE_congr_hom`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.ker_ι_app`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.exists`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.zero`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.add`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.sub`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.mul`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.sub_mem_iff`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.mem_iff_of_zero`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.restrict`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.alg`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.eq_zero_of_forall_affine`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.eq_zero_of_forall_liftsAt`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.eq_of_forall_liftsAt`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.quot_comp_factor`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.τ`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.τ_ι`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.τ_pI`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.ρ`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.presheaf_map_congr`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LiftsAt.trans`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.ρ_φ`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LocData`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.LocData.restrict`
- structure `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.le_sup`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.colon_eq`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.span_mul_le`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.pi_mul_mem`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.exists_locData`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.locData_unique`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.eLoc`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.eLoc_eq`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.eLoc_restrict`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.exists_glue`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.ker_ρ`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.injective`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.surjective`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.StepHyp.bijective`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.alg_flat`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.levels_bijective`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.map_top_apply`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.ι_appTop_alg`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.res_mem_of_ι_appTop_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.eq_zero_of_forall_ι_appTop_eq_zero`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.smodEq_pow_iff`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.bijective_alg_top`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.bijective_φ_iff`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2.bijective_appTop`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
