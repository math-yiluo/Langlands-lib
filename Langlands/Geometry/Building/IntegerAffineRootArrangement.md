# Finite spanning derivatives and integral coroots for integer-valuation data

This internal helper is an additive arbitrary-field specialization of the published
`ActualAffineRootArrangement`, `FilteredRootReflectionCells`, `ValuationAffineRootSystems`
and `NormalizerAffineRootAction` arguments. Its input is the original
`IntegerValuationBuildingData v G`, with no local-field structure or additional
hypothesis. It uses the actual root subgroups, reduced apartment and normalizer action.

Finiteness of relative roots makes the ordinary affine-root derivative set finite.
Every ordinary affine root is an extended jump functional and has an actual opposite
factor pair by the published rank-one factorization theorem. The preceding
`IntegerRootReflections` helper supplies its coroot, whose pairing 2 also proves
nonconstancy. `affineRootCoroot` chooses such a coroot for an ordinary affine root,
and `isCoroot_affineRootCoroot` records its defining property. A nonzero reduced
translation has a nonzero actual root coordinate;
V0 supplies an extended jump in that direction. The published doubling lemma puts
that jump or twice it in the ordinary roots, proving derivative spanning, including
rank zero.

An actual integral cocharacter gives the opposite-pair coroot. Every ordinary
root derivative evaluates integrally on it. The finite spanning derivative
uniqueness theorem identifies any coroot with this one, proving AR 3 without a
local-finiteness premise. The same identification realizes every affine Weyl
generator as the original normalizer action of an opposite-pair element. Closure
then proves containment of the entire affine Weyl group in the action range.

Finally, uniqueness of the integral coroot on the actual finite relative-root
system and its rational-character complement makes two same-root opposite-pair
representatives have the same full torus Weyl action. Their quotient therefore
belongs to the actual centralizer, including its central torus directions.
This will be used by the separate integer-discreteness argument.

The helper proves neither the infinite-fibre nor the bounded-finiteness clause
of corrected AR 4. It does not construct supplied building data, assert derivative
equality with all relative roots, or use a downstream chamber or cocycle theorem.
