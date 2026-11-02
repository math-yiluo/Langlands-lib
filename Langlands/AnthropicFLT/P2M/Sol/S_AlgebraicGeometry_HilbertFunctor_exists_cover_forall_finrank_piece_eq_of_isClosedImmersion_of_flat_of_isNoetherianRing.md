# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 30 here); in 19 lines the replacements `Type` (universe 0) → `Type uz` (16 places), `Scheme.{0}` → `Scheme.{uz}` (8 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing`:
let `A` be a noetherian ring and `ι : Z ⟶ ℙⁿ_A` a closed immersion with `Z` flat over `Spec A`. Then
there are finitely many `r_j ∈ A` generating the unit ideal such that for each `j` there are a
polynomial `P_j` (the Hilbert polynomial of some homogeneous ideal over some field) and `D₀` with the
following property: for every algebraically closed field `k` with `A → k` sending `r_j` to a unit,
every base change `Z_k ⊆ ℙⁿ_k` of `Z` and every homogeneous ideal `I` of `k[X₀, …, Xₙ]` whose forms are
exactly those vanishing on `Z_k` (in the charts), `dim_k piece I d = P_j(d)` for all `d ≥ D₀`.

Proof (namespace `P2mWs6C0`). Auxiliary results: a locally constant function on `Spec A` is constant on
the members of a finite cover by basic opens (`cover`); every prime is the kernel of a map to an
algebraically closed field (`geompt`); sections of a flat scheme over affine opens are flat
(`flat_sections`), so the Čech cochains of the twists `𝒪_Z(d)` for the standard affine cover are flat
(`flat_cochain`); `finrank_baseChange_eq_rankAtStalk`; base-change compatibility of the
twisting sheaves along `e : Z_k ⟶ Z` (section `Pull`: `toB`, `restrictFun_app_frameUnit`,
`preimage_pullbackChart`, `preimage_inter`, …); vanishing of high Čech cochains
(`subsingleton_cochain`). Main argument: by the ported `ProjSpace.exists_forall_subsingleton_HSucc_twist`
(Serre vanishing) and `ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion`
(sections of `𝒪_Z(d)` come from forms), for `d` large the higher Čech cohomology vanishes, so by
`Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range` `H⁰(Z, 𝒪(d))` is flat,
finite, and commutes with base change. Its rank at primes is locally constant; on each member of the
resulting finite cover it is the value of a Hilbert polynomial, and over an algebraically closed `k`
the dimension of `piece I d` equals the dimension of `H⁰(Z_k, 𝒪(d))`, which equals that rank.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.cover`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.geompt`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.flat_sections`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.inter_le_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.isAffineOpen_inter`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.flat_cochain`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.finrank_baseChange_eq_rankAtStalk`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.X_eq_mvMapGraded_mul_one`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.one_mem_zero`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.toB`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.toB_ratio`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.restrictFun_app_pullAway`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.restrictFun_app_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.restrictFun_app_eq`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.preimage_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.preimage_inter`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.toB_mk`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.subsingleton_HSucc_iff`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.P2mWs6C0.subsingleton_cochain`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_cover_forall_finrank_piece_eq_of_isClosedImmersion_of_flat_of_isNoetherianRing.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_subsingleton_HSucc_twist` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map` (Library), `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` (Library).
Other imports: none.
