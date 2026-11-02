# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 6 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Polynomial _root_.AlgebraicGeometry.Polynomial _root_.Algebra _root_.CategoryTheory.Algebra _root_.IntermediateField`: namespace `AlgebraicGeometry.Polynomial` dropped.
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Polynomial _root_.Algebra _root_.CategoryTheory.Algebra _root_.IntermediateField`: namespace `CategoryTheory.Algebra` dropped.
- Manual edit for Mathlib drift (FLT line 400, line 411 here): `IsScalarTower.of_algebraMap_eq fun a => by` is replaced by `IsScalarTower.of_algebraMap_eq (S := Localization.Away t) fun a => by`. With the project's Mathlib the middle ring of `IsScalarTower.of_algebraMap_eq` is no longer inferred from the expected type `IsScalarTower K (Localization.Away t) L` before the proof term is elaborated (it was taken to be `L`); it is given by name, `(S := Localization.Away t)`, which states the same scalar tower.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued`. Statement. `AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued`: let `K` be an infinite perfect
field, `L / K` a field extension and `t ∈ L` nonzero and transcendental over `K` with `L` finite and
separable over `K(t)`. Then for the glued scheme `glued K t` of `Def_AlgebraicCurve_CurveModelConstruction`
(two affine charts given by the integral closures of `K[t]` and `K[t⁻¹]` in `L`), the structure
morphism `gluedToBase K t` to `Spec K` is proper and smooth of relative dimension `1`; there is a
bijection `P` from the closed points to the places of `L / K` such that the image in `L` of the stalk
at each closed point `x` is the valuation ring of `P x`; and every finite set of points lies in an
affine open.

Proof. This file reruns the arguments of `Def_AlgebraicCurve_CurveModelConstruction` (there stated in
characteristic zero) under the weaker hypotheses: separability of `L / K(t)` instead of
characteristic zero, a perfect base field, and an infinite base field. Section `ChartRings` gives
the chart-ring instances (Dedekind, finite, of finite type, noetherian) from separability;
section `Glued` gives local finite type, local noetherianity, quasi-separatedness, and the
valuative criterion (`valuativeCriterion_existence_of_isSeparable`), hence properness
(`isProper_gluedToBase_of_isSeparable`). Namespace `S7A8SM` proves smoothness of relative dimension
`1` of the chart rings and of `gluedToBase` over a perfect field (formal smoothness at every prime,
rank-one Kähler differentials). Namespace `S7bP` rebuilds the bijection `gluedPlaceOfPoint'`
between closed points and places with the stalk-range property, and shows that a finite set of
points lies in one of the affine opens `Ua K t a` for some `a ∈ K` (only finitely many `a` are
excluded by each point, and `K` is infinite). The four conclusions are assembled from these.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.adjoin_inv_eq_adjoin`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.locallyOfFiniteType_gluedToBase_of_isSeparable`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.isLocallyNoetherian_glued_of_isSeparable`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.quasiSeparated_gluedToBase_of_isSeparable`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.hasLift_generic_of_mem_pullbackVS`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.hasLift_of_generic`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.gA_mem_range_of_isMaximal`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.mem_range_of_isMaximal`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.hasLift_closed_of_isMaximal`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.valuativeCriterion_existence_of_isSeparable`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.isProper_gluedToBase_of_isSeparable`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.formallySmooth_chartRing_localization_closed'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.formallySmooth_chartRing_localization_bot'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.chartRing_isSmoothAt'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.rank_kaehler_eq_one_of_finite_adjoin'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.rank_kaehler_chartRing_localization_away_eq_one'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.formallySmooth_chartRing'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.locally_isStandardSmoothOfRelativeDimension_one_chartRing'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.smoothOfRelativeDimension_one_Spec_chartRing'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7A8SM.smoothOfRelativeDimension_one_gluedToBase'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.isMaximal_iff_ne_bot'`
- private def `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.primeOfValuationSubring'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.valuationSubringAtPrime_le'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.valuationSubringAtPrime_primeOfValuationSubring'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.exists_ofHeightOneSpectrum_eq'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.mem_ofHeightOneSpectrum'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.ofHeightOneSpectrum_injective'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.ι₀_mem_closedPoints_iff'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.ιInf_mem_closedPoints_iff'`
- private def `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.primeOfι₀'`
- private def `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.primeOfιInf'`
- private def `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.gluedPlaceOfPoint'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.gluedPlaceOfPoint'_ι₀`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.gluedPlaceOfPoint'_of_not_mem`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.t_mem_of_ι₀'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.t_not_mem_of_ιInf'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.gluedPlaceOfPoint'_injective`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.gluedPlaceOfPoint'_surjective`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.gluedPlaceOfPoint'_bijective`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.range_stalk_eq_gluedPlaceOfPoint'`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.exists_placeOfPoint_glued`
- private theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.S7bP.finset_subset_affineOpen_glued_of_infinite`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction` (same contribution).
Other imports: none.
