# Actual linear descent datum from original lifted point charts

This internal construction for the finite vector-bundle filtrations of
supplied relative radicals compares actual module overlap maps by
their original point action after every pullback, using the prescribed
canonical module composition comparisons. Such compatibility is equivalent to
the normalized fixed-lift point action. Actual disjoint free presentations give
faithfulness of this compatibility. Compatibility is stable under arbitrary
pullback transport and actual composition.

`HasLinearTransitions` requires scalar preservation by the original normalized
point transition between every pair of lifts of a fixed base map, on every
test scheme. Given this property and an actual disjoint free presentation of
the cover module, `overlapIso` constructs actual module overlap isomorphisms.
Their original all-test compatibility is proved. Arbitrary pullback transport
and actual composition preserve that compatibility, so faithfulness proves
the exact naturality and cocycle equations. `linearDatum` is therefore an
actual module descent datum.

The identity transport is the original actual module morphism, by the canonical
identity pullback coherence. This proves compatibility of the actual datum
with the original unnormalized lifted point charts.
`isVectorBundleAdditive_of_linearTransitions` applies the existing effective
module descent theorem to give the exact vector-bundle additive predicate,
assuming the cover module is finite locally free, the base cover is affine,
flat, locally of finite presentation and surjective, and the original group is
affine and smooth.

The provenance is derived from actual module-map reconstruction, original point
compatibility, canonical pullback transport and effective quasicoherent module
descent. There is no supplied module cocycle, vector-bundle representer or
effectivity premise. Scalar preservation of a particular quotient's original
point transitions remains a consumer obligation.
