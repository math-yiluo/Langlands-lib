# Transport of KP model families along a building transport package

Module `Langlands.BruhatTits.IntegralModels.Transport.Family`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Geometry.Building.KPBuildingDatumTransportStatement`. It carries the supplied
models of a KP datum (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, §4.1) from the
building `B` of `G` to the building `B'` of `H`, along `f : G ≅ H` and a
`BuildingTransportPackage B B' f` (module `Transport.Package`), and shows that KP Axioms 4.1.20
and 4.1.22 survive. The source does not state this transport separately. Every model-level
step uses the transports of `Transport.Model` and `Transport.RootReflection`; every
building-level step uses the comparisons of `Transport.Package`.

Throughout, `T : BuildingTransportPackage B B' f` has torus isomorphism `T.σ`, apartment
equivalence `T.A`, building equivalence `T.Φ`, and index and facet bijections
`T.indexEquiv`, `T.facetEquiv` (images under `Φ`).

## Building-level lemmas (namespace `BuildingTransportPackage`)

- `indexEquiv_symm_ofFacet`: the index of a facet `F` of `B'` corresponds to the index of
  `T.facetEquiv.symm F` (`rfl`).
- `map_oneFixer`: `G(K)^1_Ω`, the pointwise fixer of `Ω` intersected with the common norm
  kernel, maps under `f` onto `H(K)^1_{Φ Ω}`. This uses `map_pointwiseFixer`,
  `map_rationalCommonNormKernel` and injectivity of `rationalPoints.map f.hom`.
- `map_zeroFixer`: the same for `G(K)^0_Ω`, given parahoric data `P` of `G` and `P'` of `H`
  with `P'.zeroSubgroup = f(P.zeroSubgroup)` (hypothesis `hzero`).
- `incidentEquiv F`: the facets of `B'` incident above `F` correspond to those of `B`
  incident above `Φ⁻¹ F`, by `F' ↦ Φ⁻¹ F'`.
- `hasApartmentLieWeightSignFormula_transport`: the Lie-weight sign formula of 4.1.22(3) for
  a model morphism, its quotient and torus on the subsets `A⁻¹ Fa, A⁻¹ Fa'` of the apartment of
  `B` gives the formula for the transported morphism, quotient and torus on `Fa, Fa'`. The
  proof writes a real cocharacter vector as the `σ`-transport of one for `B.S`, moves the
  point with `A_mk_vadd`, and rewrites the character specialization with
  `IntegralTorusData.transport_characterSpecialization_symm` and
  `eval_cocharacterRealCongr`.
- `hasApartmentDerivativeRootDatum_transport`: the derivative root datum of 4.1.22(6) on
  `A⁻¹ Fa` gives the datum on `Fa` for the transported quotient and torus, with the root datum
  `Droot.transport T.σ f T.comm`. The root set and the coroots are matched by
  `relativeRootsTransportEquiv`, `congr_mem_facetDerivativeRoots_iff` and the
  specialization lemmas `IntegralTorusData.transport_characterSpecialization` and
  `transport_cocharacterSpecialization`.

## The transported model family (namespace `BuildingModelFamily`)

`M.transport T : BuildingModelFamily B' R` for `M : BuildingModelFamily B R`:

- the model at an index `Ω` of `B'` is `(M.model (Φ⁻¹ Ω)).transport f` (`transport_model`,
  `rfl`); it keeps the integral group schemes and composes the generic identification
  with `f`;
- the morphism for a required pair `Ω, Ω'` of `B'` is the transport of the morphism for the
  corresponding pair of `B` (`modelMorphismRequired_symm`);
- the torus over the chart `g · A(S')` with subset `Ωa` is the transport along `(f, σ)` of the
  torus of `B` over the chart `f⁻¹(g) · A(S)` with subset `A⁻¹ Ωa` (using `symm_val_eq` and
  `conj_comm`).

Results:

- `neutralModelsIsomorphic_transport`: a neutral-model isomorphism of corresponding indices
  of `B` gives one of the indices of `B'` (`Hom.transportId`).
- `modelAxiomClauses_transport` / `satisfiesModelAxioms_transport`: if `M` satisfies KP Axiom
  4.1.20 for `P`, then `M.transport T` satisfies it for any parahoric data `P'` of `H` with
  `P'.toValuationBuildingData = B'` and `P'.zeroSubgroup = f(P.zeroSubgroup)`. Integral points
  are `f`-images (`transport_full_integralPoints`, `transport_neutral_integralPoints`) and
  fixers are `f`-images (`map_oneFixer`, `map_zeroFixer`). Facet constancy uses
  `Set.image_mono` for `Φ⁻¹`. Closure invariance rewrites both indices with
  `symm_image_translated` and `image_apartmentClosure`. The torus and simply-connected
  clauses use the transport `iff` lemmas of `Transport.Model`.
- `satisfiesGeneralMorphismAxioms_transport`: the preamble and part (1) of KP Axiom 4.1.22.

## The transported quotient family (namespace `BuildingModelQuotientFamily`)

`QF.transport T` has quotient `(QF.quotient (Φ⁻¹ F)).transport f` at a facet `F` of `B'`, with
the same radical, quotient group and projection. With `hQF : QF.FacetAxiomClauses Droot`, each
clause of KP Axiom 4.1.22 for `B'` and the root datum `Droot.transport T.σ f T.comm` is proved
as a separate theorem:

- `transport_reductive_quotients`: maximal reductive quotients (4.1.22, preamble of the facet
  clauses);
- `transport_parabolic_images`: 4.1.22(2);
- `transport_common_tori`, `transport_lie_weight_signs`: 4.1.22(3), both paragraphs. The face
  relation `IsFaceOf B'.affineRoots Fa Fa'` is pulled back to `A⁻¹ Fa, A⁻¹ Fa'` with
  `isFaceOf_image_iff`;
- `transport_reduction_preimages`: 4.1.22(4);
- `transport_parabolic_order`: 4.1.22(5). The helper lemmas `transport_facetModels_morphism`
  and `transport_incidentParabolicImage` show that the parabolic image of an incident facet
  `F'` of `B'` is the image of `incidentEquiv F F'` for `B` (by `rfl` after unfolding). So the
  map from incident facets is the old map composed with the bijection `incidentEquiv F`, and
  the bijection and order clauses follow from those of `B`;
- `transport_derivative_root_data`: 4.1.22(6). Facets of the apartment are pulled back with
  `isFacet_apartment_image_iff`;
- `transport_positive_radicals`: 4.1.22(7).

`facetAxiomClauses_transport` assembles these, and `satisfiesMorphismAxioms_transport` gives
full KP Axiom 4.1.22 (`SatisfiesMorphismAxioms`) for `QF.transport T` and the transported
root datum.
