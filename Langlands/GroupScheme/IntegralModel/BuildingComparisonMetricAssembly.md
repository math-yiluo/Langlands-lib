# Construct a comparison metric from the five geometric axioms

This internal assembly removes the supplied metric from the corresponding
constructors in `BuildingComparisonAssembly`. The field is any nonarchimedean
local field `F : Type u`; the actual group `G`, integral model `M`, generic
identification and rational-point group are unchanged.

`BuildingComparison.ofParahoricApartmentSpecialPoint` takes one
`P : ParahoricBuildingData G`, its polysimplicial realization `R` and apartment
splitting `T`, and the seven predicates used to express the five geometric
axioms of `MetricRealizationStatement`:

* `P.SatisfiesBuildingAxiom R` (4.1.1);
* `P.HasBoundedOpenStabilizers` (4.1.2);
* `P.SatisfiesAffineApartmentAxiom T` (4.1.4);
* `P.HasRootReflections`, `P.SatisfiesApartmentAxioms` and
  `P.HasCompatibleApartmentFacets` (4.1.6);
* `P.HasTitsSystem` (4.1.9).

It also retains actual opposite-factor-pair existence for `P.i`, a special
apartment point `x`, and the equality
`M.integralPoints = P.compactStabilizer (P.apartmentMap x)`.
There is no metric, apartment-map injectivity or fixed-point uniqueness input.

The published theorem `Langlands.Geometry.Building.metricRealization`,
from `MetricRealizationProof`, constructs a complete NPC metric on precisely
`P.toValuationBuildingData.ReducedBuilding`, with its existing rational-point
action isometric and its orbit maps continuous in exactly
`rationalPointTopology F G.X`. Classical choice selects this metric realization.
The AS 6 witness `hC.injective` supplies apartment-map injectivity, and
`hR.isBuilding` supplies the abstract building condition. Applying the existing
`ofApartmentSpecialPoint` then constructs `BuildingComparison M`. In particular,
special-to-vertex and the apartment-to-global fixed-point argument supply
vertexhood and uniqueness for the original `M.integralPoints`.
The building and distinguished point are preserved by definitional equality,
as recorded by the two simplification theorems.

`BuildingComparison.ofParahoricApartmentFamilyModelIso` obtains the exact
model-image equality from a supplied `BuildingModelFamily` and its full-model
points clause, together with an identity-generic `IntegralModel.Iso` between
the original `M` and the full model at the singleton facet of
`P.apartmentMap x`. It composes `Iso.integralPoints_eq` with
`integralPoints_vertexModelIndex` and applies the first constructor. Thus it
preserves the actual supplied generic identification and does not replace the
full model by its neutral component.

The provenance is internal composition of published metric, special-point,
common-apartment and model-family results; this module asserts no new
correspondence with original literature. Constructing the parahoric data,
realization, splitting, five axiom witnesses, opposite pairs, special point
and original-model image equality or compatible family isomorphism remains
necessary. This conditional assembly does not prove
`BuildingComparisonStatement` and does not assert the full ten-axiom package.
