# Structure statements for the scheme-theoretic derived subgroup

This module gives four separate proposition declarations and their conjunction
`Langlands.GroupScheme.DerivedSubgroupStructureStatement`. Each is a `Prop`-valued
definition, not a proof. The module uses the actual group schemes
`Langlands.GroupScheme S = Grp (Over S)` and the subgroup functor and
`IsDerivedSubgroup` predicate from `Derived.Basic`. It constructs no representing
group and selects no inclusion.

The source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Definition 6.16, Propositions 6.17–6.18 and Corollary 6.19(a)–(b), printed p.129 /
PDF p.145, supply the quotient definition, its commutator-generated
characterization for affine or smooth groups, and the structure assertions.
The affine coordinate description after Corollary 6.19, printed p.130 /
PDF p.146, is another source for the closed representing subgroup. Expressing
these claims through the intersection definition and an arbitrary exhibiting
inclusion is a derived reformulation of that source.

Every declaration quantifies over arbitrary fields `k : Type u` and actual
groups `G` over `Spec (CommRingCat.of k)`. The only common geometric assumptions
are `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`. Affineness also
supplies quasi-compactness, so this is the affine finite-type field scope.
The universe `u` is arbitrary. No perfection, splitting, connectedness or
smoothness assumption enters closed representability or field base change.

- `DerivedSubgroupRepresentabilityStatement` asserts unconditionally in this
  scope that there exist an actual field group scheme `D` and an actual
  homomorphism `d : D ⟶ G`, with `D` affine and locally of finite type and
  `IsDerivedSubgroup d`. The last predicate requires a closed immersion and
  equality of the entire range functor with `derivedSubgroup G`. This includes
  nonsmooth and disconnected `G`.
- `DerivedSubgroupFieldBaseChangeStatement` quantifies over every field
  extension `K/k`, expressed by `[Algebra k K]`, and every actual exhibiting
  `d : D ⟶ G`. With `b = Spec.map (CommRingCat.ofHom (algebraMap k K))`, it asserts
  that `(GroupScheme.baseChange b).map d` exhibits the derived subgroup of the
  actual pullback of `G`. It also asserts
  `(derivedSubgroup G).baseChange b =
  derivedSubgroup ((GroupScheme.baseChange b).obj G)`, using the published
  subgroup-functor base-change map. Both equalities concern all test schemes
  over the relevant base, including nonreduced tests.
- `DerivedSubgroupSmoothnessStatement` says that for every such actual
  exhibiting `d`, `Smooth G.X.hom` implies `Smooth D.X.hom`.
- `DerivedSubgroupConnectednessStatement` says independently that
  `ConnectedSpace G.X.left` implies `ConnectedSpace D.X.left`. It has no
  smoothness hypothesis.

The three compatibility declarations quantify over an exhibiting inclusion
because the first declaration separately asks for its unconditional existence.
They do not assume a compatibility assertion or a structure conclusion as a
premise. The elementary containment, minimality and normality proofs in
`Derived.Basic` do not prove these targets. Substantive representability and
structure proofs remain separate obligations.

Annihilation after arbitrary algebra scalar extension, including the character
specialization, is a separate statement unit. Milne Corollary 6.19(d) obtains
that assertion from faithfully flat local commutator generation in (c), which
the elementary intersection lemmas do not provide.

Milne Remark 6.23, printed p.131 / PDF p.147, distinguishes the scheme-theoretic
derived group from the abstract commutator subgroup of rational points. These
declarations assert no equality between those point groups, no rational-point
quotient formula and no surjectivity on rational points.

The retained official author errata
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was checked with the source. Its displayed Chapter 6 correction concerns
Example 6.48. The HTML has a commented-out caution about 6.19(c)–(e), not a
displayed correction; it is not used to narrow these field statements.
