# Split unipotence of represented products of split normal subgroups

`Langlands.GroupScheme.SplitNormalFppfProductStatement.{u}` is a Prop-valued
statement for every universe `u`. Let `k : Type u` be a field and let `G` be
an actual group scheme over `Spec (CommRingCat.of k)` with
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`. Let `i : H ⟶ G` and
`j : N ⟶ G` be homomorphisms of actual group schemes over the same base.
Each must satisfy the following:

- it is a closed subgroup (`IsClosedSubgroup`);
- its source is smooth over the base and has connected underlying space;
- its all-test image `SubgroupFunctor.range` is normal;
- its source satisfies the published `RelativeRoot.IsSplitUnipotent`.

Let `p : P ⟶ G` be any homomorphism with
`SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
(SubgroupFunctor.range j) p`, where `P` is smooth over the base and has
connected underlying space. The statement asserts
`RelativeRoot.IsSplitUnipotent P`.

The published `IsFppfProduct` makes `p` a closed subgroup. On every relative
scheme test, its image consists exactly of the points that factor fppf locally
as a point of the first image times a point of the second. All predicates are
imported unchanged. `IsSplitUnipotent` is the existence of a finite
`RelativeRoot.HasSplitSeries`. Its endpoint is trivial on all tests. Each step
has a smooth connected normal closed kernel and a represented fppf quotient
whose all-test point functor is naturally the one-dimensional additive group.
The statement does not construct the product. In this field setting, the
published `SmoothConnectedNormalFppfProductExistenceStatement` asks for one.
Smoothness and connectedness of `P` are hypotheses here.
The statement places no perfectness or characteristic restriction on `k`.

## Provenance

This is a derived interface statement. It isolates the closure property needed
to prove `SplitUnipotentRadicalExistenceStatement`. Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), assert existence of the
maximal split smooth connected unipotent normal subgroup in the discussion
preceding Proposition 2.2.4, printed p.63 (PDF p.89), "due to dimension
reasons and the normality requirement". That argument uses the fact that the
product of two such subgroups is again split. The source does not prove that
fact on that page.

The intended mathematical justification is Milne, *Algebraic Groups* (2017),
§16.g, printed p.343 (PDF p.359). Quotients of split solvable groups are split,
because the nontrivial quotients of `Ga` are isomorphic to `Ga`
(Exercise 14-3). Extensions of split solvable groups are split. For the product
`HN`, the quotient `HN/N` is a quotient of the split group `H`, and `N` is
split, so `HN` is split. Milne's Definition 14.61 (printed p.299) defines split
unipotent groups by subnormal series with `Ga` quotients. Definition 6.33
(printed p.132) defines split solvable groups by such series with `Ga` or `Gm`
quotients. The Lean statement uses the published finite normal fppf-quotient
series instead, with each step normal in its immediate predecessor.

Registered sources: `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54` (printed
page `p` is PDF page `p + 26`); `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0` (printed
page `p` is PDF page `p + 16`).

The file defines a proposition and supplies no proof.
