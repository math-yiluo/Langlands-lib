# Transport of actual reduced-norm-one groups

Author: Worker 165.

This is an internal derived construction for Task 5442. It reuses the actual
unconditional reduced norm and its determinant comparison from the published
`Langlands.Algebra.ReducedNorm` module. It introduces no classification
hypothesis and places no restriction on the field characteristic.

The reduced degree is the square root of the vector-space dimension, so an
algebra isomorphism preserves it. For a finite basis of the first algebra,
the reduced-norm polynomial in its transported basis is equal to the original
polynomial. The proof transports a finite Galois splitting chart of the second
algebra to the first, reindexes the square matrices by the reduced-degree
equality, and compares coefficients in that splitting field. Reindexing rows
and columns together preserves determinant.

Base-changed coordinates of corresponding tensors in the two bases agree.
Evaluating the equal coordinate polynomials therefore proves preservation of
the reduced norm on every commutative coefficient algebra, including algebras
with nilpotents. The hypotheses supply finite-dimensional central simple
algebras and an actual algebra isomorphism; they contain no supplied norm
compatibility or group-scheme isomorphism.

For an algebra isomorphism `e : A ≃ₐ[K] B`,
`Langlands.CentralSimple.reducedNormOneAlgEquiv e R` restricts the induced
isomorphism of tensor-unit groups to their actual reduced-norm-one subgroups.
The inverse uses the inverse tensor algebra isomorphism and norm preservation.
This construction applies to every commutative coefficient algebra `R`, in an
independent universe.

The group-scheme construction lies in
`Langlands.GroupScheme.CentralSimpleUnits`. The theorem
`normOneAlgEquiv_naturality` proves that tensor transport commutes with
restriction along every morphism of test schemes, by induction on tensors.
Composing with the existing `normOnePointsEquiv` comparisons gives
`normOneAlgEquivPointIso e T`, a multiplicative equivalence between the actual
groups of `T`-points of `normOne K A` and `normOne K B`.
The theorem `normOneAlgEquivPointIso_naturality` proves its naturality for
every scheme over `Spec K`; the tests need not be affine or reduced.

The internal helper `Langlands.GroupScheme.exists_isoOfPoints_with_formulas`
packages the published Yoneda construction `isoOfPoints` together with its
forward and inverse point formulas. Specializing it proves
`exists_normOneAlgEquivIso`: there is an actual group-scheme isomorphism whose
forward maps are `normOneAlgEquivPointIso e T` and whose inverse maps are their
inverses, simultaneously on every test scheme.
The definition `normOneAlgEquivIso e` selects an isomorphism from this existence
proof. Thus the construction provides an isomorphism in the category of group
schemes over `Spec K`, with compatibility established on all tests.

The construction supports the later passage from an algebra decomposition to
the actual reduced-norm-one group in family (i). Existence of that decomposition
and the local rank-one classification remain separate obligations.
