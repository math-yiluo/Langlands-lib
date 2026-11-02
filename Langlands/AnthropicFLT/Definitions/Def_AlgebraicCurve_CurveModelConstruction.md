# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicCurve_CurveModelConstruction.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Construction of a smooth proper model of a function field in one variable over an algebraically
closed field of characteristic zero by gluing two affine charts (namespace
`AlgebraicCurve.CurveModel`). Throughout, `L / K` is a field extension and `t ∈ L` (with
`t ≠ 0` as `Fact`, and `L` finite over `K(t)` and over `K(t⁻¹)` where needed).

- Section `Charts`: the chart rings `chartRing K {t}`, `chartRing K {t⁻¹}` and `chartRing K {t, t⁻¹}`
  (integral closures, from `Def_JacJ1_ChartAlgebra`), the inclusions `incl₀`, `inclInf`, the elements
  `tChart`, `tInvChart`; the overlap ring is the localization of each chart ring at `t`, respectively
  `t⁻¹` (`isLocalization_away_incl₀`, `isLocalization_away_inclInf`); their spectra `X₀`, `XInf`,
  `XOverlap` with the open immersions `f₀`, `fInf`.
- Section `Glue`: `glued K t`, the pushout of `f₀` and `fInf`, with open immersions `ι₀`, `ιInf`
  (`glue_condition`) and `gluedToBase : glued K t ⟶ Spec K`; every point lies in one of the two
  charts, which meet.
- Sections `Qualities`, `FiniteType`, `Compact`, `Noetherian`: the glued scheme is integral, locally of
  finite type, Jacobson, quasi-compact and locally noetherian over `Spec K`, and
  `smoothOfRelativeDimension_one_gluedToBase` (for transcendental `t`, via
  `Def_AlgebraicCurve_CurveModelSmooth`); its function field is identified with `L`
  (`gluedFunctionFieldIsoOverlap`, `gluedFunctionFieldEquiv`, compatible with `K`); closed points of the
  charts are the nonzero primes (`isMaximal_iff_ne_bot`, `ι₀_mem_closedPoints_iff`, …).
- Sections `Overlap`, `StalkRange`, `PlaceMap`: points of the overlap; the image of each stalk in `L`
  is the localization of the chart ring (`range_ffEquiv_symm_comp_algebraMap_stalk`); the map
  `gluedPlaceOfPoint` from closed points to places of `L / K` (through `primeOfι₀`, `primeOfιInf`
  and `primeEquivChartPlaces`) is bijective (`gluedPlaceOfPoint_bijective`), with stalk images the
  valuation rings (`range_stalk_eq_gluedPlaceOfPoint`).
- Sections `RingLemmas`, `SpecLemmas`, `LiftLemma`, `Generic`, `Closed`, `ClosedLift`, `Uniqueness`:
  the existence and uniqueness parts of the valuative criterion for `gluedToBase`
  (`valuativeCriterion_existence`, `valuativeCriterion_uniqueness`): a valuative square whose
  generic point maps to the generic point, or to a closed point of a chart, has a lift
  (`hasLift_generic`, `hasLift_closed`), and lifts are unique; hence `isProper_gluedToBase`.
- Sections `ChartGerms`, `LocalSections`, `Values`, `Affine`: for `a ∈ K`, an affine open `Ua K t a`
  (the union of `D(t - a) ⊆ X₀` and `D(1 - a t⁻¹) ⊆ XInf`, affine because two glued sections generate
  the unit ideal, `isAffineOpen_Ua`), and every point lies outside only finitely many `Ua K t a`
  (`finite_setOf_not_mem_Ua`).
- Section `Packaging`: every finite set of points lies in an affine open
  (`finset_subset_affineOpen_glued`), and `ofGenerator K t ht : CurveModel K L` for transcendental
  `t`.
- Section `TowerPack`: for `L` finite over `RatFunc K` (with compatible algebra structures),
  `towerGenerator` (the image of `X`) is a nonzero transcendental element with `L` finite over the
  fields it generates, and `nonempty_body K L : Nonempty (CurveModel K L)` when `K` is algebraically
  closed of characteristic zero.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicCurve.CurveModel.singleton_subset_pair`
- theorem `AlgebraicCurve.CurveModel.singleton_inv_subset_pair`
- abbrev `AlgebraicCurve.CurveModel.incl₀`
- abbrev `AlgebraicCurve.CurveModel.inclInf`
- def `AlgebraicCurve.CurveModel.tChart`
- def `AlgebraicCurve.CurveModel.tInvChart`
- theorem `AlgebraicCurve.CurveModel.coe_tChart`
- theorem `AlgebraicCurve.CurveModel.coe_tInvChart`
- theorem `AlgebraicCurve.CurveModel.isUnit_incl₀_tChart`
- theorem `AlgebraicCurve.CurveModel.isUnit_inclInf_tInvChart`
- theorem `AlgebraicCurve.CurveModel.isLocalization_away_incl₀`
- theorem `AlgebraicCurve.CurveModel.isLocalization_away_inclInf`
- abbrev `AlgebraicCurve.CurveModel.X₀`
- abbrev `AlgebraicCurve.CurveModel.XInf`
- abbrev `AlgebraicCurve.CurveModel.XOverlap`
- abbrev `AlgebraicCurve.CurveModel.f₀`
- abbrev `AlgebraicCurve.CurveModel.fInf`
- instance `AlgebraicCurve.CurveModel.isOpenImmersion_f₀`
- instance `AlgebraicCurve.CurveModel.isOpenImmersion_fInf`
- def `AlgebraicCurve.CurveModel.glued`
- def `AlgebraicCurve.CurveModel.ι₀`
- def `AlgebraicCurve.CurveModel.ιInf`
- theorem `AlgebraicCurve.CurveModel.glue_condition`
- instance `AlgebraicCurve.CurveModel.isOpenImmersion_ι₀`
- instance `AlgebraicCurve.CurveModel.isOpenImmersion_ιInf`
- theorem `AlgebraicCurve.CurveModel.f₀_toBase_eq_fInf_toBase`
- def `AlgebraicCurve.CurveModel.gluedToBase`
- theorem `AlgebraicCurve.CurveModel.ι₀_gluedToBase`
- theorem `AlgebraicCurve.CurveModel.ιInf_gluedToBase`
- theorem `AlgebraicCurve.CurveModel.smoothOfRelativeDimension_one_gluedToBase_of_charts`
- theorem `AlgebraicCurve.CurveModel.mem_range_ι₀_or_mem_range_ιInf`
- theorem `AlgebraicCurve.CurveModel.range_ιInf_inter_range_ι₀_nonempty`
- instance `AlgebraicCurve.CurveModel.isIntegral_glued`
- theorem `AlgebraicCurve.CurveModel.smoothOfRelativeDimension_one_gluedToBase`
- instance `AlgebraicCurve.CurveModel.isFractionRing_overlap`
- instance `AlgebraicCurve.CurveModel.algebra_overlap_functionField`
- instance `AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField`
- def `AlgebraicCurve.CurveModel.overlapFunctionFieldAlgEquiv`
- def `AlgebraicCurve.CurveModel.ιU`
- theorem `AlgebraicCurve.CurveModel.ιU_eq`
- theorem `AlgebraicCurve.CurveModel.ιU_eq'`
- instance `AlgebraicCurve.CurveModel.isOpenImmersion_ιU`
- theorem `AlgebraicCurve.CurveModel.ιU_gluedToBase`
- theorem `AlgebraicCurve.CurveModel.ιU_genericPoint`
- def `AlgebraicCurve.CurveModel.gluedFunctionFieldIsoOverlap`
- def `AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv`
- theorem `AlgebraicCurve.CurveModel.gluedFunctionFieldIsoOverlap_baseToFunctionField`
- theorem `AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv_algebraMap`
- instance `AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing`
- theorem `AlgebraicCurve.CurveModel.not_isField_chartRing`
- theorem `AlgebraicCurve.CurveModel.isMaximal_iff_ne_bot`
- instance `AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase`
- instance `AlgebraicCurve.CurveModel.jacobsonSpace_glued`
- theorem `AlgebraicCurve.CurveModel.ι₀_mem_closedPoints_iff`
- theorem `AlgebraicCurve.CurveModel.ιInf_mem_closedPoints_iff`
- theorem `AlgebraicCurve.CurveModel.ι₀_eq_ιInf_iff`
- theorem `AlgebraicCurve.CurveModel.range_fInf`
- theorem `AlgebraicCurve.CurveModel.range_f₀`
- theorem `AlgebraicCurve.CurveModel.ιInf_mem_range_ι₀_iff`
- theorem `AlgebraicCurve.CurveModel.ι₀_mem_range_ιInf_iff`
- scoped instance `AlgebraicCurve.CurveModel.stalkAlgebra_spec`
- scoped instance `AlgebraicCurve.CurveModel.isLocalization_stalk_spec`
- theorem `AlgebraicCurve.CurveModel.specMap_genericPoint`
- def `AlgebraicCurve.CurveModel.thetaHom`
- theorem `AlgebraicCurve.CurveModel.thetaHom_toStalk`
- theorem `AlgebraicCurve.CurveModel.thetaHom_mk'`
- theorem `AlgebraicCurve.CurveModel.range_thetaHom`
- theorem `AlgebraicCurve.CurveModel.ffEquiv_symm_algebraMap_stalk`
- theorem `AlgebraicCurve.CurveModel.range_ffEquiv_symm_comp_algebraMap_stalk`
- theorem `AlgebraicCurve.CurveModel.transcendental_inv`
- def `AlgebraicCurve.CurveModel.primeOfι₀`
- def `AlgebraicCurve.CurveModel.primeOfιInf`
- theorem `AlgebraicCurve.CurveModel.primeOfι₀_asIdeal`
- theorem `AlgebraicCurve.CurveModel.primeOfιInf_asIdeal`
- theorem `AlgebraicCurve.CurveModel.mem_range_ιInf_of_not_mem_range_ι₀`
- def `AlgebraicCurve.CurveModel.gluedPlaceOfPoint`
- theorem `AlgebraicCurve.CurveModel.gluedPlaceOfPoint_ι₀`
- theorem `AlgebraicCurve.CurveModel.gluedPlaceOfPoint_of_not_mem`
- theorem `AlgebraicCurve.CurveModel.t_mem_of_ι₀`
- theorem `AlgebraicCurve.CurveModel.t_not_mem_of_ιInf`
- theorem `AlgebraicCurve.CurveModel.tInvChart_mem_of_not_mem_range`
- theorem `AlgebraicCurve.CurveModel.gluedPlaceOfPoint_injective`
- theorem `AlgebraicCurve.CurveModel.gluedPlaceOfPoint_surjective`
- theorem `AlgebraicCurve.CurveModel.gluedPlaceOfPoint_bijective`
- theorem `AlgebraicCurve.CurveModel.range_stalk_eq_gluedPlaceOfPoint`
- instance `AlgebraicCurve.CurveModel.compactSpace_glued`
- instance `AlgebraicCurve.CurveModel.quasiCompact_gluedToBase`
- instance `AlgebraicCurve.CurveModel.isLocallyNoetherian_glued`
- instance `AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase`
- def `AlgebraicCurve.CurveModel.liftOfRange`
- theorem `AlgebraicCurve.CurveModel.liftOfRange_spec`
- theorem `AlgebraicCurve.CurveModel.comp_liftOfRange`
- theorem `AlgebraicCurve.CurveModel.SpecMap_cancel`
- theorem `AlgebraicCurve.CurveModel.fromSpecStalk_comp`
- theorem `AlgebraicCurve.CurveModel.exists_eq_SpecMap_comp_fromSpecStalk`
- theorem `AlgebraicCurve.CurveModel.hasLift_of_range`
- theorem `AlgebraicCurve.CurveModel.ringCompat`
- theorem `AlgebraicCurve.CurveModel.stalkMap_toStalk_genericPoint`
- def `AlgebraicCurve.CurveModel.gL`
- theorem `AlgebraicCurve.CurveModel.gL_ffEquiv_symm`
- def `AlgebraicCurve.CurveModel.pullbackVS`
- theorem `AlgebraicCurve.CurveModel.mem_pullbackVS_iff`
- theorem `AlgebraicCurve.CurveModel.algebraMap_mem_pullbackVS`
- theorem `AlgebraicCurve.CurveModel.hasLift_generic_top`
- theorem `AlgebraicCurve.CurveModel.hasLift_generic_centre`
- theorem `AlgebraicCurve.CurveModel.hasLift_generic`
- def `AlgebraicCurve.CurveModel.stalkChartEquiv`
- def `AlgebraicCurve.CurveModel.φA`
- def `AlgebraicCurve.CurveModel.gA`
- theorem `AlgebraicCurve.CurveModel.φA_stalkMap`
- theorem `AlgebraicCurve.CurveModel.stalkMap_chart_toStalk`
- theorem `AlgebraicCurve.CurveModel.gA_algebraMap`
- theorem `AlgebraicCurve.CurveModel.gA_eq_zero`
- theorem `AlgebraicCurve.CurveModel.gA_mem_range`
- theorem `AlgebraicCurve.CurveModel.exists_gA_mul_gA_eq_one`
- theorem `AlgebraicCurve.CurveModel.φ_mem_range`
- theorem `AlgebraicCurve.CurveModel.hasLift_closed`
- theorem `AlgebraicCurve.CurveModel.valuativeCriterion_existence`
- theorem `AlgebraicCurve.CurveModel.range_subset_of_closedPoint_mem`
- theorem `AlgebraicCurve.CurveModel.liftStruct_eq_of_mem_range`
- theorem `AlgebraicCurve.CurveModel.incl₀_tChart_mul_inclInf_tInvChart`
- theorem `AlgebraicCurve.CurveModel.false_of_liftStruct_cross`
- theorem `AlgebraicCurve.CurveModel.valuativeCriterion_uniqueness`
- instance `AlgebraicCurve.CurveModel.isProper_gluedToBase`
- def `AlgebraicCurve.CurveModel.secTop`
- theorem `AlgebraicCurve.CurveModel.mem_basicOpen_secTop`
- theorem `AlgebraicCurve.CurveModel.germ_res_secTop`
- theorem `AlgebraicCurve.CurveModel.stalkMap_germ_appIso_inv`
- def `AlgebraicCurve.CurveModel.cSec`
- theorem `AlgebraicCurve.CurveModel.stalkMap_germ_cSec`
- theorem `AlgebraicCurve.CurveModel.isUnit_stalkMap_iff`
- theorem `AlgebraicCurve.CurveModel.thetaHom_algebraMap`
- theorem `AlgebraicCurve.CurveModel.ffEquiv_symm_germ_appIso_inv`
- def `AlgebraicCurve.CurveModel.tma`
- def `AlgebraicCurve.CurveModel.gInf`
- theorem `AlgebraicCurve.CurveModel.coe_tma`
- theorem `AlgebraicCurve.CurveModel.coe_gInf`
- theorem `AlgebraicCurve.CurveModel.incl₀_tma`
- theorem `AlgebraicCurve.CurveModel.gInf_add`
- theorem `AlgebraicCurve.CurveModel.tma_add`
- def `AlgebraicCurve.CurveModel.U₁`
- def `AlgebraicCurve.CurveModel.U₂`
- theorem `AlgebraicCurve.CurveModel.mem_U₁_iff`
- theorem `AlgebraicCurve.CurveModel.mem_U₂_iff`
- theorem `AlgebraicCurve.CurveModel.isUnit_res_tma`
- theorem `AlgebraicCurve.CurveModel.isUnit_res_gInf`
- def `AlgebraicCurve.CurveModel.σ₁`
- def `AlgebraicCurve.CurveModel.σ₂`
- theorem `AlgebraicCurve.CurveModel.germ_σ₁_mul`
- theorem `AlgebraicCurve.CurveModel.germ_σ₂_mul`
- def `AlgebraicCurve.CurveModel.V₁`
- def `AlgebraicCurve.CurveModel.V₂`
- def `AlgebraicCurve.CurveModel.Ua`
- theorem `AlgebraicCurve.CurveModel.isAffineOpen_V₁`
- theorem `AlgebraicCurve.CurveModel.isAffineOpen_V₂`
- def `AlgebraicCurve.CurveModel.f₁'`
- def `AlgebraicCurve.CurveModel.f₂'`
- theorem `AlgebraicCurve.CurveModel.one_sub_ne_zero`
- theorem `AlgebraicCurve.CurveModel.genericPoint_mem_U₁`
- theorem `AlgebraicCurve.CurveModel.genericPoint_mem_U₂`
- theorem `AlgebraicCurve.CurveModel.genericPoint_mem`
- theorem `AlgebraicCurve.CurveModel.val_f₁'`
- theorem `AlgebraicCurve.CurveModel.val_f₂'`
- theorem `AlgebraicCurve.CurveModel.res_f₁'_eq_res_f₂'`
- def `AlgebraicCurve.CurveModel.cover`
- theorem `AlgebraicCurve.CurveModel.exists_glued_section`
- theorem `AlgebraicCurve.CurveModel.f₀_appTop_secTop`
- theorem `AlgebraicCurve.CurveModel.fInf_appTop_secTop`
- theorem `AlgebraicCurve.CurveModel.tma_not_mem_iff`
- def `AlgebraicCurve.CurveModel.fTwo`
- theorem `AlgebraicCurve.CurveModel.span_eq_top`
- theorem `AlgebraicCurve.CurveModel.stalkMap_germ_f_V₁`
- theorem `AlgebraicCurve.CurveModel.stalkMap_germ_f_V₂`
- theorem `AlgebraicCurve.CurveModel.stalkMap_germ_fTwo_V₁`
- theorem `AlgebraicCurve.CurveModel.stalkMap_germ_fTwo_V₂`
- theorem `AlgebraicCurve.CurveModel.basicOpen_f`
- theorem `AlgebraicCurve.CurveModel.basicOpen_fTwo`
- theorem `AlgebraicCurve.CurveModel.isAffineOpen_Ua_of`
- theorem `AlgebraicCurve.CurveModel.isAffineOpen_Ua`
- theorem `AlgebraicCurve.CurveModel.ιInf_mem_Ua`
- theorem `AlgebraicCurve.CurveModel.ι₀_mem_Ua`
- theorem `AlgebraicCurve.CurveModel.subsingleton_gInf_mem`
- theorem `AlgebraicCurve.CurveModel.finite_setOf_not_mem_Ua`
- theorem `AlgebraicCurve.CurveModel.finset_subset_affineOpen_glued`
- def `AlgebraicCurve.CurveModel.ofGenerator`
- def `AlgebraicCurve.CurveModel.towerGenerator`
- theorem `AlgebraicCurve.CurveModel.towerGenerator_ne_zero`
- theorem `AlgebraicCurve.CurveModel.transcendental_towerGenerator`
- theorem `AlgebraicCurve.CurveModel.coe_algEquivOfTranscendental_towerGenerator`
- theorem `AlgebraicCurve.CurveModel.adjoin_simple_inv_eq`
- theorem `AlgebraicCurve.CurveModel.finiteDimensional_congr`
- theorem `AlgebraicCurve.CurveModel.finiteDimensional_adjoin_towerGenerator`
- theorem `AlgebraicCurve.CurveModel.nonempty_body`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelSmooth` (same contribution).
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.ValuativeCriterion`, `Mathlib.Algebra.GCDMonoid.IntegrallyClosed`, `Mathlib.AlgebraicGeometry.FunctionField`, `Mathlib.AlgebraicGeometry.AlgClosed.Basic`, `Mathlib.AlgebraicGeometry.Limits`, `Mathlib.FieldTheory.RatFunc.AsPolynomial`.
