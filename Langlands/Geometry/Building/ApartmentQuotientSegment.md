# Chart-independent segments in the original apartment quotient

This internal construction defines affine interpolation in the existing
`KPApartmentData.ReducedBuilding` quotient. The closed proposition
`Langlands.Geometry.Building.UnramifiedFixedSegmentStatement.{u}` and its theorem
`unramifiedFixedSegment` specialize it to the original inputs of the unramified
fixed-point problem. The universe is arbitrary, and there is no characteristic
restriction.

## General hypotheses and construction

The general section works over a field `k`, with a commutative group scheme `S`,
a group scheme `G`, a morphism `i : S.toGrp ⟶ G` whose underlying scheme morphism
is monic, an affine structure morphism for `G`, a function `ω : kˣ → ℝ`, and
`D : KPApartmentData i ω`. The construction `chosenSegmentPoint` also takes
`hcommon : D.HasCommonApartments`: any two quotient points have representatives
in one rational translate of the original apartment. Its chart-independence
theorems require `hG : IsConnectedReductive G` and
`hi : IsMaximalSplitTorus i`.

`PairApartmentCoordinates` and `commonApartmentCoordinates`, imported from
`ApartmentQuotientRootDistance`, record and choose a rational element `g` and
apartment points `a,b` with endpoints `g • D.apartmentMap a` and
`g • D.apartmentMap b`. For `t : Set.Icc (0 : ℝ) 1`, `chosenSegmentPoint` is

`g • D.apartmentMap (AffineMap.lineMap a b (t : ℝ))`.

The universal translated-apartment formula
`chosenSegmentPoint_smul_apartmentMap` proves that this expression agrees with
interpolation in every such chart. `chosenSegmentPoint_apartmentMap` gives the
formula in the original apartment. The existing quotient, apartment map and
rational-point action are used throughout.

`chosenSegmentPoint_zero` and `chosenSegmentPoint_one` recover the endpoints.
`chosenSegmentPoint_smul` proves equivariance for the actual rational-point
action, with the same real parameter. Consequently
`smul_chosenSegmentPoint_eq_of_endpoints_fixed` says that an element fixing both
endpoints fixes each interpolated point.

`chosenSegment` is the range of the interpolation map for its two endpoints.
Both endpoints belong to this set. The theorem
`mem_pointwiseFixer_chosenSegment_iff` identifies membership in its actual
pointwise fixer with fixation of both endpoints. Finally,
`eq_chosenSegmentPoint_of_smul_apartmentMap` proves uniqueness of a map satisfying
the universal chart formula. In particular the chart formula determines the map
despite the choice of common-apartment coordinates.

## Implemented chart comparison

The main transport lemma `smul_apartmentMap_lineMap_of_two_eq` starts with a
rational element `g` and four apartment points satisfying
`g • D.apartmentMap a = D.apartmentMap x` and
`g • D.apartmentMap b = D.apartmentMap y`.
The published
`exists_normalizer_eq_of_two_apartmentMap_eq` supplies one actual normalizer
`n` with `n • a = x` and `n • b = y`. Thus `n⁻¹ * g` fixes both apartment
images. The published `smul_apartmentMap_lineMap_eq` makes it fix every point
of their closed segment. Multiplying back by `n` and using
`normalizerAffineEquiv.apply_lineMap` gives

`g • D.apartmentMap (lineMap a b t) = D.apartmentMap (lineMap x y t)`.

To compare a chosen chart with an arbitrary chart translated by `g`, apply this
lemma to `g⁻¹ * c.translate`, where `c` is the chosen coordinate datum.
Cancellation gives the universal chart formula. Common apartments and that
formula then prove rational equivariance and uniqueness. The pointwise-fixer
equivalence uses endpoint membership for one direction and equivariance for the
other. The parameter restriction to the closed unit interval is retained in all
these conclusions.

## Actual coefficient action

The coefficient section works with a field extension `K/k`, schemes and map
`i` over `k`, and apartment data `D` for the literal base change of `i` to `K`.
It assumes monicity of this base-changed map and
`hD : KPApartmentData.GaloisStable k K i D`. Connected reductivity and maximal
splitness are required over `K`, together with `D.HasCommonApartments`.

`galoisAction_lineMap` is the line-map identity for the published actual affine
equivalence `galoisAffineAction`. The theorem
`galoisQuotientAction_chosenSegmentPoint` proves, for every `k`-algebra
automorphism `σ` of `K`, that the existing `galoisQuotientAction` commutes with
interpolation and preserves its parameter.

The proof writes both endpoints in one translated apartment, applies the
universal chart formula, and uses the published
`galoisQuotientAction_smul` and `galoisQuotientAction_apartmentMap`. These replace
the translated chart by the one translated by `rationalConjugate σ g`.
The affine line-map identity transports its two coordinates, and the universal
chart formula identifies the result. The theorem
`galoisQuotientAction_chosenSegmentPoint_eq_of_endpoints_fixed` then proves
pointwise coefficient fixation of the segment when both endpoints are fixed by
every coefficient automorphism. These are the actual coefficient maps on the
same quotient as the endpoints.

## Original unramified inputs

`MaximalUnramified.hasCommonApartments_of_apartment` works with a nonarchimedean
local field `F` and its actual inertia fixed field `K = inertiaFixedField F`.
The inputs are a connected reductive `F`-group `G`, a commutative `F`-group
scheme `T` and map `iT`, maximal splitness of its literal base change to `K`,
the supplied upper apartment datum `D`, the actual centralizer datum `C`, and
`IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C`.
The monomorphism instance is obtained from maximal splitness. The affine
structure morphism for `G` is explicit in this helper and is derived from
connected reductivity in the closed statement.

The helper forms
`MaximalUnramified.buildingDataOfApartment hG hiT D C h6` and applies the
published `MaximalUnramified.commonApartments` to exactly that building datum.
Its apartment is the original `D`. Therefore the specialization adds no
common-apartment premise. It uses the canonical integer valuation on `K` and
assumes no local-field structure on `K`.

`UnramifiedFixedSegmentStatement` quantifies over these original inputs and
the supplied `hD : GaloisStable F K iT D`. It asserts existence of an
interpolation map in `D.ReducedBuilding` with six properties:

1. The universal translated-apartment formula.
2. The two endpoint identities.
3. Equivariance for the original `G(K)` action.
4. Pointwise fixation of its range exactly when both endpoints are fixed.
5. Equivariance for the actual coefficient action of every `F`-algebra
   automorphism of `K`.
6. Fixation of every interpolated point by all those automorphisms whenever
   both endpoints are coefficient-fixed.

The implementing theorem derives common apartments as above and derives
connected reductivity over `K` using
`IsConnectedReductive.baseChange_of_algebraicExtension`. It chooses the general
`chosenSegmentPoint` and applies its established properties. The last clause
composes coefficient equivariance with the two endpoint equalities.

## Provenance and scope

This is an internal composition of published Library results; it claims no
translation of an external source. Its principal inputs are the simultaneous
normalizer comparison in `GenericApartmentPairNormalizer`, two-point fixation in
`ApartmentFacetClosureFixing`, coordinate choice in `ApartmentQuotientRootDistance`,
the actual affine coefficient and quotient actions in
`GaloisApartmentQuotientAction`, common apartments in
`IntegerValuationCommonApartmentsProof`, and the packaging constructor in
`UnramifiedApartmentModelInput`. The underlying normalizer affine map and group
actions are the published ones.

No norm, finite-root-type, metric, curvature or integral-model premise is
added. The result supplies affine segments and their fixation properties; it
does not prove a metric or identify these segments with geodesics of a metric
structure. The given Galois stability of the apartment datum remains an input.
It constructs no descended facet or segment model, residue morphism, lifted
torus or prescribed-point special apartment. In particular
`UnramifiedFixedPointSplitTorusStatement` remains open. The four building-descent
statements prohibited by the host contract and theorems consuming them are not
proof inputs.
