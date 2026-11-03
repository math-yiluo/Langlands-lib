# A Borel containing a given smooth connected solvable subgroup

`Langlands.GroupScheme.SolvableSubgroupBorelContainmentStatement` states that,
over every algebraically closed field `k : Type u`, a given smooth connected
solvable closed subgroup of a smooth affine connected group scheme lies in a
Borel subgroup. The universe and characteristic are arbitrary.

More precisely, the input includes the actual group schemes `H` and `G` and
the actual homomorphism `j : H ⟶ G`, with `IsClosedSubgroup j`,
`Smooth H.X.hom`, `ConnectedSpace H.X.left`, and `IsSolvableGroupScheme H`.
The output is an actual group scheme `B`, an embedding `i : B ⟶ G` satisfying
`IsBorelSubgroup i`, and a homomorphism `f : H ⟶ B` with `f ≫ i = j`.
Thus the same given subgroup is contained in the resulting Borel.

The predicates are the published ones in `Absolute.Borel`: solvability is
solvability of the abstract group of geometric points, and a Borel is a smooth
connected solvable closed subgroup maximal among such subgroups by actual
factorizations. The conclusion is an equation of group-scheme morphisms; it
is stronger than containment of rational points.

The source is Milne, *Algebraic Groups* (2017), Definition 17.6 and the
paragraph immediately following it, printed pp.353–354 (one-based PDF
pp.369–370), together with the opening containment step of the proof of
Theorem 17.10, printed p.355 (PDF p.371). The section assumes a connected
group variety over an algebraically closed field. The maximality argument
used there extends the given smooth connected solvable subgroup to one of
largest dimension among its overgroups. The statement here makes the given
embedding and its resulting factorization explicit in the published
group-scheme categories. The registered official errata snapshot dated
2 November 2026 has no correction to these passages.

A proof may instead minimize coordinate-kernel height among admissible
overgroups of `j`, using the published `Absolute.BorelExistenceCoordinates`
lemmas. That is a proposed implementation route, not a proof supplied by
this statement module. Neither Borel conjugacy nor maximal-torus conjugacy
is a premise of this proposition.

For the maximal-torus conjugacy application, the smoothness, connectedness,
and solvability of a torus must still be established before this proposition
can be applied to its embedding. This statement does not supply those
properties, the conjugacy of Borel subgroups, or the conjugacy of maximal
tori in a solvable group. It also differs from the assertion that every
Borel contains some ambient maximal torus, and from the reverse assertion
that a smooth subgroup containing a Borel is connected.
