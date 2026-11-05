# Woundness under separable algebraic field extension

Authors: Worker 1328 and Worker 1609.

`Langlands.GroupScheme.unipotentWoundSeparableExtension.{u}` proves exactly
the unchanged published proposition
`Langlands.GroupScheme.UnipotentWoundSeparableExtensionStatement.{u}`.
For every separable algebraic extension `K/k`, a smooth connected affine
unipotent actual group scheme over `k` has only constant affine-line maps
if and only if its actual scalar extension to `K` does.

The implemented proof composes three published results.
`RelativeRoot.commutativePTorsionVectorFactor` proves the vector-factor
proposition without an extra premise.
`UnipotentWoundCriterionReduction.criterion_of_vectorFactor` applies that
result to prove the exact all-field central additive-subgroup criterion.
In prime characteristic, this criterion extracts a smooth central
commutative subgroup killed by the characteristic and uses its vector
factor to obtain a central closed additive line whenever affine-line
constancy fails. Its characteristic-zero branch is already unconditional.

`woundSeparableFromCriterion` then applies this proved criterion. For the
forward implication, ground-field affine-line constancy excludes a central
closed additive line after separable extension: such a line transports to
the separable closure, where the central Galois norm obstruction gives a
contradiction. This obstruction uses a finite Galois coefficient model and
its nonzero tangent, without requiring the original extension to be finite.
The criterion over `K` yields constancy of the actual base-changed group.
Smoothness, affineness, connectedness and representation-based unipotence
are transported by the reduction. For the reverse implication, faithfully
flat pullback reflects constancy of every affine-line morphism.

The final theorem has no criterion or vector-factor premise. Its universe
`u` is arbitrary, both characteristics are included, and neither field
needs to be perfect or infinite. The extension may be infinite, including
a separable closure. The maps in the constancy predicate are all
affine-line scheme morphisms; they need not be group homomorphisms.
Scalar extension remains the original group-scheme pullback.

This final assembly is internally derived from the named published
results. The source provenance and scope of the proposition remain in
`UnipotentWoundSeparableExtensionStatement.md`; this proof follows the
implemented criterion, norm-obstruction and reflection route.
