# The central additive-subgroup criterion over every field

`Langlands.GroupScheme.unipotentWoundCriterion.{u}` proves exactly
`Langlands.GroupScheme.UnipotentWoundCriterionStatement.{u}`. The statement
and all its imports are unchanged.

For every field `k : Type u` and actual smooth connected affine group scheme
`G` satisfying the existing representation-based `IsUnipotent` predicate,
every actual affine-line scheme morphism to `G` is constant if and only if
`G` has no actual central closed subgroup with natural one-dimensional vector
coordinates on every relative scheme test. The theorem includes finite and
imperfect fields and both characteristic zero and positive characteristic.
It has no additional structural premise.

The implemented proof applies the published
`UnipotentWoundCriterionReduction.criterion_of_vectorFactor` to the published
`RelativeRoot.commutativePTorsionVectorFactor`. The latter has exactly the
`CommutativePTorsionVectorFactorStatement.{u}` type required by the reduction.
Thus this application discharges its remaining argument.

The reduction already proves the forward implication by showing that an
additive closed subgroup would contradict affine-line constancy. For the
reverse implication in prime characteristic, it extracts a nontrivial
pointed family in a smooth connected affine central commutative subgroup
killed by `p`. The vector-factor theorem decomposes that subgroup over the
original field into a vector factor and a complement whose affine-line maps
become constant over the separable closure. Smooth-family density and field
descent make the complement projection trivial. Nontriviality forces the
vector factor to have positive dimension; a coordinate line gives the
required actual central closed additive subgroup.

The reduction's characteristic-zero branch extracts a nontrivial central
commutative subgroup, proves its unipotence for the original predicate, and
uses perfect-field splitting and the commutative vector classification to
obtain a positive-dimensional vector group. A closed coordinate line again
gives the subgroup. The field-characteristic dichotomy combines these
branches in the exact named target.

This final application is an internal deduction from those published proofs.
The source-backed target is the all-field analogue of conditions (1) and (2)
of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition B.3.2, printed p.572, one-based PDF p.598. Its Appendix B assumes
positive characteristic; the characteristic-zero branch is a derived
extension. The source is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The Lean proof follows the published reduction and vector-factor construction
described above; it makes no claim about the other conclusions of B.3.2.
