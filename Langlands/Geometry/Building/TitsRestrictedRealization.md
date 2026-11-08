# The polysimplicial realization given by the restricted Tits building

Fix actual `P : ParahoricBuildingData G` over a nonarchimedean local field at
universe `u`, a chamber `Ca` of the apartment, a Weyl-group datum
`π : N(F) ∩ G(F)^0 →* W` and `Sgen ⊆ W`. Assume the full supplied
`hT : P.IsBuildingTitsSystem Ca π Sgen`, the existing form of KP Axiom 4.1.9.
It contains the saturated Tits system
`(G(F)^0, G(F)^0_{Ca}, N(F) ∩ G(F)^0, Sgen)` with finite `Sgen`, and the
bijection `F ↦ G(F)^0_F` from the facets of the original valuation quotient
onto the admissible parabolic subgroups. Under it, the original incidence
`F ≺ F'` is `G(F)^0_{F'} ≤ G(F)^0_F`, and the stabilizer sets of the
apartments `h · A(S)` are the restricted apartments. This module transfers the
frozen Tits-level results `TitsRestrictedPolysimplicial`,
`TitsRestrictedApartments` and `TitsRestrictedAutomorphisms` to the original
quotient. It follows KP Definition 1.5.20 and Proposition 1.5.18: `B(G)` is
the restricted building of this Tits system, hence polysimplicial. No apartment
axioms, injectivity of the apartment map or affine independence of vertices
are used. All results are internal deductions from these imported
definitions and proved APIs.

## The realization

`finite_sgen` turns `hT.finite` into `Finite Sgen`.
`facetAdmissibleEquiv` is the equivalence from `BuildingFacet B` to admissible
parabolic subgroups given by Mathlib's `Set.BijOn.equiv` applied to the
existing bijection `hT.bijOn_facetZeroStabilizer`. It sends a facet to its
actual stabilizer `P.facetZeroStabilizer`.

`titsRealization` is the `PolysimplicialRealization` with index type
`Component Sgen` (the irreducible components of `Sgen`). Its vertex sets are
the component vertices of the Tits system, and its complex is the restricted
polysimplicial complex. The realization map is the inverse of
`restrictedFacetOrderIso`, followed by `OrderDual.ofDual` and the inverse of
`facetAdmissibleEquiv`. `coe_titsRealization_realize_symm` records, by
definition, that the facet of the complex realizing a facet `F` of `B(G)` is
the product of the component simplices of `G(F)^0_F`.
`restrictedBox_facetZeroStabilizer_eq_iff` deduces that these products
determine the facet.

## Face compatibility, apartments and the building clause

`titsRealization_isFaceCompatible`: writing complex facets as realizations of
facets `E`, `E'` of `B(G)`, inclusion of products is
`G(F)^0_{E'} ≤ G(F)^0_E` (`restrictedBox_subset_iff`). This is the original
`FacetPrecedes E E'` by `hT.facetPrecedes_iff`.

`exists_titsRealization_apartmentComplex_eq`: for an apartment
`Y = h · A(S)`, the stabilizers of the facets contained in `Y` form an element
of the existing `apartmentFacetStabilizers`. By
`hT.apartmentFacetStabilizers_eq` this is a restricted apartment based at some
`a ∈ G(F)^0`. The realized facets inside `Y` are then exactly
`restrictedApartmentBoxes a`. `isPolysimplicial_titsRealization_apartmentComplex`
follows from `isPolysimplicial_restrictedApartmentBoxes`.

`titsRealization_isBuilding` applies the existing full-Tits theorem
`realization_isBuilding` (from `AffineTitsRealizationBuilding`), with the
face compatibility, the polysimplicial apartments and the explicit premise
`hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s}`.

## The action

This section assumes `[P.zeroSubgroup.Normal]`, normality of `G(F)^0` in
`G(F)`. It is not proved here. Conjugation by a rational point `g` is then the
Mathlib automorphism `MulAut.conjNormal g` of `G(F)^0`.

`facetZeroStabilizer_translate` proves
`G(F)^0_{g F} = g G(F)^0_F g⁻¹`, using `Subgroup.mem_map_equiv`,
`MulAut.conjNormal_symm_apply` and the original action on facets.
`isAdmissibleParabolic_map_conjNormal_iff` deduces that this conjugation
preserves admissible parabolic subgroups in both directions, because they are
exactly the facet stabilizers.

`titsRealization_isPolysimplicialAction` proves the existing
`IsPolysimplicialAction`. By the existing criterion
`isPolysimplicialAction_iff_respectsCoordinateFibers`, one needs a component
permutation `σ` under which the canonical vertex permutation
`vertexTranslateEquiv g` respects coordinate fibers.
`exists_componentPerm` supplies `σ`. The existing uniqueness lemma
`vertexTranslateEquiv_unique` identifies `vertexTranslateEquiv g` with the
explicit `autVertexEquiv`. Its hypothesis reduces, by `restrictedBox_map`,
`facetZeroStabilizer_translate` and `restrictedBox_facetZeroStabilizer_eq_iff`,
to `F' = g F`. `respectsCoordinateFibers_autVertexEquiv` finishes the proof.

`satisfiesBuildingAxiom_titsRealization` assembles the existing structure
`SatisfiesBuildingAxiom` (KP Axiom 4.1.1 for one group). It takes `hadm`,
normality of `G(F)^0`, `HasTorusApartmentCorrespondence` and
`HasNormalizerApartmentStabilizer` as hypotheses. The last two fields are
passed through unchanged.

`satisfiesBuildingAxiom_affineTitsRealization` specializes to the literal
affine Tits datum `π = P.affineTitsProjection`,
`Sgen = P.chamberSimpleInAffinePart e Ca`, as in the existing
`affineTitsRealizationBuilding`. Under an affine Weyl comparison `e`, the
corrected affine root system hypothesis and a chamber `Ca`, the existing
`isAdmissibleType_singleton_chamberSimpleInAffinePart` discharges `hadm`.

## Scope

All results remain conditional on the supplied full Tits comparison `hT`. The
action and the assembled axiom also need normality of `G(F)^0`, the torus
correspondence and the normalizer stabilizer, and the general theorem needs
singleton admissibility. None of these, nor actual valuation data for an
arbitrary connected reductive group, is constructed here. The module does not
prove `RootValuationBuildingConstructionStatement`.
