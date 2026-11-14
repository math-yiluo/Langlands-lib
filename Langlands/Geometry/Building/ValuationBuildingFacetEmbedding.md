# Facets along an apartment-compatible building map

This is an internal geometric construction for the unramified facet-order
proof. It is derived from the published facet partitions, apartment
injections, and common-apartment interface. It does not state a new
literature assertion or prove the special-fibre parabolic correspondence.

All declarations are in
`Langlands.Geometry.Building.ValuationBuildingData`, at arbitrary universe
`u`. The source is `B : ValuationBuildingData G` over a nonarchimedean
local field `F`. The target is
`C : IntegerValuationBuildingData v H` over an arbitrary field `K`, with
an integer-valued valuation `v`. The fields and groups are in the same
arbitrary universe.

The supplied comparison data are:

- a homomorphism `φ : rationalPoints G →* rationalPoints H`;
- a point map `e : B.ReducedBuilding → C.ReducedBuilding`;
- a real affine map `a : B.Apartment →ᵃ[ℝ] C.Apartment`;
- equivariance `e (g • x) = φ g • e x`;
- compatibility `e (B.apartmentMap x) = C.apartmentMap (a x)`;
- the exact facet pullback identity
  `a ⁻¹' facet C.affineRoots (a x) = facet B.affineRoots x`
  for every source apartment point `x`.

The global results also assume `B.SatisfiesApartmentAxioms` and
`B.HasCommonApartments`. No injectivity or surjectivity of `e`, `a`, or
`φ` is an additional hypothesis. Source and target apartment injection
follow from their connected-reductive building data, using the published
`KPApartmentData.apartmentMap_injective` and
`IntegerValuationBuildingData.apartmentMap_injective`.

## Construction and exact results

`facetLift B C e Fc` chooses a point of the nonempty source facet `Fc`
and takes the unique full target facet containing its image.
`facetLift_of_mem` proves independence of the chosen point: every
`x ∈ Fc` gives `facetLift B C e Fc = C.buildingFacetAt (e x)`.

`preimage_facetLift` proves the literal equality of sets
`e ⁻¹' (facetLift B C e Fc).val = Fc.val`.
`image_facetLift` consequently gives
`e '' Fc.val = (facetLift B C e Fc).val ∩ Set.range e`.
In particular `facetLift_injective` says that different source facets
have different lifted full facets.

The exported equivalence `facetRangeEquiv` identifies the actual source
facet type `BuildingFacet B` with
`{Fd : C.BuildingFacet // (Fd.val ∩ Set.range e).Nonempty}`.
The codomain keeps the full target facet and the property of meeting the
point-map image. The lemma `facetRangeEquiv_val` identifies its forward
map with `facetLift`.

## Implemented proof

On a source translated apartment, equivariance and apartment compatibility
rewrite the comparison as the target translated chart with group element
`φ g` and apartment map `a`. The published
`buildingFacetAt_translatedApartmentMap` identifies the containing target
facet with the chart image of the affine-root facet. Target chart
injectivity and the assumed facet pullback identity then prove
`mem_buildingFacetAt_image_chart_iff`.

For arbitrary source points `x` and `y`, `B.HasCommonApartments` gives a
single translated source apartment containing both. The chart result,
the source containing-facet formula, and source chart injectivity prove
`mem_buildingFacetAt_image_iff`: `e y` belongs to the full facet through
`e x` exactly when `y` belongs to the source facet through `x`.
Source facet uniqueness turns this into `preimage_facetLift`, and the
standard set image/preimage identity proves `image_facetLift`.

Taking preimages proves injectivity of `facetLift`. A target full facet
meeting `Set.range e` contains some `e x`; the source facet through `x`
lifts to it by target facet uniqueness. This proves
`facetLift_surjective_on_range`. `Equiv.ofBijective` then constructs
`facetRangeEquiv`.

## Application to unramified descent and limits

For the data of `UnramifiedFacetParabolicOrderStatement`, take
`H = baseChanged F (inertiaFixedField F) G` and
`φ = rationalExtend F (inertiaFixedField F) G`.
The statement supplies equivariance, apartment compatibility, and the
facet pullback identity explicitly. Its building axiom supplies
`B.HasCommonApartments` through the published
`SatisfiesBuildingAxiom.hasCommonApartments`.

When the image of `e` is the fixed set of the supplied semilinear action,
`image_facetLift` identifies the source facet image with the fixed part
of its lifted full facet, and the equivalence indexes exactly the full
facets meeting that fixed set. Replacing `Set.range e` by the fixed set
requires that separate equality. This module does not assert invariance
of the lifted full facets, incidence preservation, or any assertion about
algebraic parabolic subgroups, integral models, or special fibres. Those
remain separate obligations of the task.
