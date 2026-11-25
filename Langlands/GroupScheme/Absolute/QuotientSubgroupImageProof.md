# Proof: algebraically closed quotient subgroup images

`Langlands.GroupScheme.algClosedQuotientSubgroupImage :
AlgClosedQuotientSubgroupImageStatement.{u}` proves the unchanged statement
[`Absolute.QuotientSubgroupImageStatement`](QuotientSubgroupImageStatement.md)
for every universe `u`. Let `k : Type u` be algebraically closed, let `G` and
`Q` be smooth connected affine group schemes over `k`, and let `q : G ⟶ Q`
be flat and surjective on underlying scheme spaces.

For a supplied smooth closed image `j : H' ⟶ Q` of `i : H ⟶ G`, encoded
by a scheme-surjective homomorphism `f : H ⟶ H'` with
`i ≫ q = f ≫ j`, the theorem preserves parabolic, Borel and maximal smooth
connected unipotent subgroups. It also preserves maximal tori, with the
factor map a morphism of commutative group schemes as in the target.
Conversely, every prescribed subgroup of `Q` of each of these four kinds
has such a surjective image presentation from a subgroup of `G` of the
same kind. These are all eight clauses of the target, with no additional
hypotheses.

The module first proves the assembly lemma
`algClosedQuotientSubgroupImage_of_quotientParabolicImage`, which takes
`QuotientParabolicImageStatement.{u}` as an explicit premise. The exact
theorem supplies that premise with the published theorem
[`quotientParabolicImage`](../Rational/QuotientParabolicImageProof.md).

Over an algebraically closed field the algebraic-closure base map is an
isomorphism. Hence a Borel is a geometric Borel, and the supplied
arbitrary-field image statement gives Borel image preservation as well as
parabolic image preservation. The actual schematic image of every Borel
therefore gives a Borel image presentation.

[`QuotientMaximalUnipotent`](QuotientMaximalUnipotent.md) derives
maximal-unipotent image preservation from these Borel presentations, using
classification by Borel unipotent parts and solvable unipotent-part images.
[`QuotientTorusImageAmbient`](QuotientTorusImageAmbient.md) derives
maximal-torus image preservation from Borel images and solvable
maximal-torus images.

In [`QuotientSubgroupRealization`](QuotientSubgroupRealization.md), Borel
realization follows from Borel conjugacy and lifting rational conjugating
points. [`QuotientParabolicRealization`](QuotientParabolicRealization.md)
uses the reduced actual inverse image of a prescribed parabolic, which
contains a Borel lifted by the Borel realization theorem. Maximal-unipotent
and maximal-torus realization follow from image preservation, existence,
conjugacy and rational-point lifting. The public maximal-unipotent
predicate unfolds to the target statement's local predicate, and the torus
realization lemma returns actual morphisms of commutative group schemes.

The provenance is Milne, *Algebraic Groups* (2017), Proposition 17.20
(printed pp.357–358), with Proposition 17.14 for maximal-unipotent
classification and Proposition 17.69 for the arbitrary-field image input.
The registered source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The subordinate paired modules describe the implemented geometric proofs.
This module adds only the assembly lemma and the exact theorem.
