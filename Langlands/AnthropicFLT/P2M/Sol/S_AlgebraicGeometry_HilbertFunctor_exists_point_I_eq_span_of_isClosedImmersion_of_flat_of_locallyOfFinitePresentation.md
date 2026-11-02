# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 36 here); in 11 lines the replacements `Type` (universe 0) → `Type uz` (9 places), `Scheme.{0}` → `Scheme.{uz}` (6 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`:
for a Hilbert polynomial `P` there is `D₀` such that for every `m ≥ D₀`, every ring `A` and every
closed subscheme `ι : Z ⟶ ℙⁿ_A`, flat and locally of finite presentation over `Spec A`, all of whose
geometric fibres come from points with Hilbert function `hilbertFunctionOf n P m`: the ideal generated
by the forms of degree `≥ m` vanishing on `Z` (in all charts) is the ideal of a point over `A` with
this Hilbert function.

Proof (namespace `PointDescentAssembly`). `exists_theta`: dehomogenization gives `A`-linear maps
`Θ_d` from forms of degree `d` to Čech `0`-cochains of the twist `𝒪_Z(d)`, landing in `H⁰`
(`res_top_mem_H0`), with `Θ_d F = 0` iff `F` vanishes on all charts (`theta_eq_zero_iff`), compatible
with multiplication (`chart_vanish_mul`), and surjective onto `H⁰` when all `H⁰` classes come from
forms (`exists_theta_eq_of_forall_H0`). Take `D₀` from the regularity theorem
`HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf`.
Descend `Z` to a noetherian `A₀` of finite type over `ℤ` (ported
`ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`).
`local_data` and the ported `Module.finite_projective_ker_baseChange_of_forall_exists_isUnit` show
that for `d ≥ m` the `H⁰` of `𝒪_Z(d)` is finite projective of rank `hilbertFunctionOf n P m d` and that
`Θ_d` onto it is surjective (fibrewise regularity). Then
`HilbertFunctor.exists_point_I_eq_span_of_forall_surjective_of_forall_projective` gives the point.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.res_top_mem_H0`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.exists_theta`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.vertex₀`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.pullbackChart_le_inter_vertex₀`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.theta_eq_zero_iff`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.chart_vanish_mul`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.exists_theta_eq_of_forall_H0`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.PointDescentAssembly.local_data`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_forall_surjective_of_forall_projective` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback` (same contribution).
Other imports: `Mathlib`.
