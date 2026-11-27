# Jacquet vanishing for uniform quasicuspidal inducing blocks

`Langlands.AllFieldBZ.CuspidalSupport.uniformJacquetVanishing` proves
`UniformJacquetVanishingStatement F T` for every nonarchimedean local
field package `F`, every topological datum `T` and both universes
`uF` and `uV`. The block shapes, the actual normalized induction and
Jacquet functors and the smooth subquotient relation are those of the
statement.

## Combinatorial step

Let every block of \(B\) have size \(r\) and let the block \(j\) of
\(C\) have size not divisible by \(r\). The private lemma
`no_associated_refinement` shows that no standard refinement \(S\) of
\(C\) has its Levi subgroup, embedded in \(G = GL_n\), equal to a
permutation conjugate of the Levi subgroup of \(B\). Suppose such
\(S\) and a permutation \(w\) existed. By
`Langlands.Geometric.refinedLevi_map_leviEmbedding` the refined Levi
is the Levi of the flattened shape `C.flatten S`, so \(w\) conjugates
the Levi of \(B\) onto it (`ConjugatesLevi`). The induced map of
blocks is surjective (`TotalConjugatingCount.blockMap_surjective`) and
preserves sizes (`TotalConjugatingCount.size_blockMap`), so every
block of `C.flatten S` has size \(r\). Through
`BlockShape.flatten_size_flattenBlockEquiv` each block of the refinement
\(S_j\) of the block \(j\) then has size \(r\), and since these
sizes sum to the size of the block \(j\), that size is
\(r\) times the number of blocks of \(S_j\), a contradiction.

## Vanishing of the Jacquet module of the induction

The private lemma `jacquet_induced_zero` takes a positive rank \(n\)
and the absence of such a refinement. It applies the all-field
geometric lemma `Langlands.AllFieldBZ.Geometric.padicGeometricLemma`,
which gives a finite filtration of the actual normalized Jacquet
module of the actual normalized induction, natural in the inducing
representation, whose grades are naturally isomorphic to the
geometric pieces attached to the minimal representatives \(w\) of the
double cosets of the two standard parabolics. For each grade,
`source_refinement_proper_of_no_associated_refinement` shows that the
source refinement of \(B\) belonging to the piece is proper. Then
`geometricPieceFunctor_subsingleton_of_proper_source` shows the piece
is zero: quasicuspidality of the inducing representation makes its
normalized Jacquet module along the proper refinement zero, and the
transport and refined induction that follow preserve zero. The
natural isomorphism of the grade with the piece makes the grade zero,
and `RepFunctorFiltration.subsingleton_atObject` concludes that the
whole Jacquet module of the induction is zero.

## The subquotient

In `uniformJacquetVanishing` the rank \(n\) is positive because it is
the sum of the block sizes of \(C\), and the block \(j\) has positive
size. The theorem `normalizedJacquetSubquotient` shows that the
normalized Jacquet functor along \(C\) carries the smooth subquotient
\(\pi\) of the induction to a subquotient of the Jacquet module of the
induction, and a subquotient of a zero representation is zero
(`Langlands.CuspidalSupport.subsingleton_of_isSubquotient`).

## Sources

The vanishing argument is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), Corollary
2.13(a), printed p. 449 (`bernstein-zelevinsky-1977-induced-i`): if
the target has no standard subgroup associated to the quasicuspidal
source Levi, the composite of induction and Jacquet functor is zero,
read off from the geometric lemma 2.12. The statement above is its
case of a source Levi with equal blocks, where association is ruled
out by divisibility. Zelevinsky, *Induced representations of
reductive p-adic groups II* (1980), Proposition 3.4, printed
pp. 181–182 (`zelevinsky-1980-induced-ii`), uses this divisibility
argument for a segment and a two-block target.
