# Commutative normal subgroups and reductivity

Author: Worker 696.

`Langlands.GroupScheme.reductiveCommutativeNormalTorus` proves exactly the
published `ReductiveCommutativeNormalTorusStatement.{u}` in arbitrary universe
`u`. It adds no hypotheses and does not change the target or its imports.

For every field `k` and smooth connected affine group scheme `G` over `Spec k`,
connected reductivity implies that every smooth connected commutative normal
closed subgroup is a torus. Over a perfect field, the latter property implies
connected reductivity. Closedness and normality have the target's original
meaning on every test scheme; commutativity is `IsCommMonObj`.

## Implemented proof

For the forward direction, pass to the algebraic closure. Closedness,
smoothness, connectedness, commutativity and normality are preserved by this
base change. A commutative group scheme is solvable. The published
`algClosedReductiveNormalSolvableTorus` therefore makes the pulled-back
subgroup a torus. `IsTorus.of_baseChange` gives the assertion over `k`.
Affineness of the subgroup follows from its closed inclusion in `G`.

For the converse, first prove that `G` is pseudo-reductive. Suppose that a
smooth connected normal unipotent closed subgroup `i : U → G` has nontrivial
range. Normality and monicity give an actual automorphic action of `G` on
`U` by conjugation. Apply the published
`hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent` to obtain a
nontrivial smooth connected central closed subgroup `z : Z → U` stable under
this action. The central monomorphism makes `Z` commutative. Stability
under conjugation makes the composite inclusion `z ≫ i` normal in `G`;
the proof verifies that assertion on every test scheme using the actual
conjugation morphism. By the assumed property of `G`, `Z` is a torus.
The published `IsUnipotent.range_eq_bot_of_isTorus` says that every
homomorphism from a torus to the affine unipotent group `U` has trivial
range, contradicting the choice of `z`. Thus `G` is pseudo-reductive.
Finally `perfectFieldPseudoReductive` converts pseudo-reductivity to
connected reductivity over the perfect field.

## Provenance

This is an internal composition of published Library proofs. The target
Markdown relates the assertion to Milne, *Algebraic Groups* (2017),
Proposition 19.12. The implemented converse uses the last nontrivial
universal lower-central commutator construction from
[`UnipotentSmoothCenter`](../Rational/UnipotentSmoothCenter.md), rather
than constructing the last term of the derived series. That imported
construction supplies its smooth connected central subgroup over every
field and proves stability under the supplied affine group action.
Perfectness is needed here only in the final comparison of
pseudo-reductivity and reductivity. The forward direction uses
[`AlgClosedNormalSolvableTorusProof`](../Rational/AlgClosedNormalSolvableTorusProof.md).
