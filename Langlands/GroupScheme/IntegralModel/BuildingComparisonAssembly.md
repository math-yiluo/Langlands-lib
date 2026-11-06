# Assemble a comparison on the original quotient and supplied model

This internal construction connects the published metric, common-apartment,
special-point, integral-model-isomorphism and model-family interfaces. It is
polymorphic in the field universe `u`. Its inputs are supplied data and proved
predicates on one actual `ValuationBuildingData G` quotient. It constructs
conditional comparisons for the original supplied integral model `M`.

`isFacet_singleton_of_isVertex` unpacks the existing definition of a building
vertex. An apartment vertex has singleton affine facet; translating that
singleton gives precisely the singleton of the original building point.
`vertexModelIndex` is the existing subset-family index of this actual facet.
Its underlying subset is definitionally the original singleton, so no new
point, apartment presentation or independently chosen model is introduced.

`oneFixer_vertexModelIndex` identifies the family's one-group fixer at this
index with the existing `compactStabilizer`. The pointwise fixer of a
singleton is the point stabilizer; commuting the intersection with the same
`rationalCommonNormKernel G` gives equality of the actual subgroups of
`rationalPoints G`. `integralPoints_vertexModelIndex` then specializes the
supplied family's full-points clause to this index. It concerns the full
model, its original generic identification and its original integral-point
image. It does not substitute the neutral model or its zero-group fixer.

`BuildingComparison.ofApartmentSpecialPoint` takes a metric realization on
this same quotient, a supplied polysimplicial realization satisfying
`AbstractBuilding.IsBuilding`, the apartment axioms, actual opposite-factor
pair existence, apartment-map injectivity, a supplied special apartment
point `x`, and equality of the original `M.integralPoints` with the existing
norm-one stabilizer of `B.apartmentMap x`.

The constructed comparison retains the supplied metric, its completeness,
NPC inequality, isometric action and continuous orbit maps. Its
rational-point topology is exactly `rationalPointTopology F G.X`. The
published special-to-vertex theorem supplies vertexhood. The point is
special with translating element `1`. For uniqueness, common apartments are
derived from the supplied abstract building axiom. The published
apartment-to-global reduction then applies to the apartment singleton
calculation at the supplied special point, using the apartment axioms,
actual opposite pairs and injectivity. Rewriting the original model image
by its stated subgroup equality gives the comparison's `unique_fixed`
field. The building and distinguished point are recorded by definitional
equalities.

`BuildingComparison.ofApartmentFamilyModelIso` obtains that exact subgroup
equality from an identity-generic `IntegralModel.Iso` between `M` and the
full singleton-facet model of a supplied `BuildingModelFamily`, together
with the family's full-points clause. `Iso.integralPoints_eq` preserves the
two supplied generic identifications, rather than using an abstract
isomorphism of models. Thus the result is `BuildingComparison M` for the
original model.

The provenance is internal: these definitions compose the published
quotient, facet, point-fixer, metric, common-apartment, special-point,
model-family and compatible-model-isomorphism results. No new assertion
from the original literature is used.

This unit constructs neither building data nor a metric, realization,
special point, opposite pairs, model family or compatible model
isomorphism. Its apartment axioms and other geometric premises remain
explicit. It proves no existence statement for every supplied good
integral model and leaves `BuildingComparisonStatement` unproved. It
also does not assert the corrected full ten-axiom validity package.
