# Extended affine root systems for integer-valuation building data

This compatibility module imports the canonical declarations from
`IntegerValuationExtendedAffineRoots`, which prove AS2 for the extended affine
roots of `IntegerValuationBuildingData`. The shared proofs adapt
`ValuationAffineRootSystems` to explicit integer-valued valuations. The
affine-root-system conclusion assumes an explicit unit of order one, which is
already available over the maximal unramified field as
`MaximalUnramified.exists_order_eq_one`. This result does not assume apartment
axioms or an unproved filtration statement.

The proof identifies the derivative set with the range of the actual relative
root forms using V0 and the extended-root jump characterization. Finiteness
follows from finiteness of the relative roots. Spanning follows from
`IntegerValuationBuildingData.span_derivativeRoots_affineRoots` and inclusion of
ordinary affine roots in extended affine roots.

The coroot of an actual opposite factor pair is a coroot of the extended
system: normalizer conjugation preserves extended roots, and
`normalizerAffineEquiv_reflectionElement` identifies that conjugation with the
affine reflection. Every extended affine root comes from such a pair by
`reflectionAffineRoots_eq` and `hasOppositeFactorPairs`. Uniqueness of coroots for
finite spanning derivative sets then reduces integrality to
`rootForm_reflectionCoroot_integral`.

Bounded finiteness follows from
`finite_bounded_reflectionFunctionals_of_oppositePairs` by taking a finite union
over the relative roots. Infinitude of each derivative fibre uses the published
`infinite_fiber_extendedAffineRoots` and its explicit order-one-unit hypothesis.
These facts supply every field of
`AffineRootSystem.IsAffineRootSystemWithRankZero`, including rank zero.
