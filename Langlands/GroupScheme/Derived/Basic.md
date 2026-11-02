# The scheme-theoretic derived subgroup functor

This module defines an intersection of actual closed subgroup functors for
`Langlands.GroupScheme S = Grp (Over S)`. It also proves its elementary subgroup
properties. It does not construct a representing group scheme.

The source is J. S. Milne, *Algebraic Groups* (2017), Definition 6.16 and
Propositions 6.17–6.18, printed p.129 / PDF p.145, registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Milne defines `DG` as the intersection of normal algebraic subgroups whose
algebraic quotients are commutative. Proposition 6.17 says the resulting quotient
is commutative; Proposition 6.18 identifies `DG`, when `G` is affine or smooth,
with the smallest algebraic subgroup containing the commutator morphism. The
intersection here is a derived reformulation of that latter description. The
arbitrary-base definitions are internal extensions of the interface; no
arbitrary-base representability or quotient comparison is asserted.

For a subgroup functor `F`, `SubgroupFunctor.ContainsCommutators F` says that
`x * y * x⁻¹ * y⁻¹` belongs to `F(T)` for every `T : Over S` and every pair of
`T`-points of `G`. Non-affine and nonreduced test schemes are included.

`derivedSubgroup G` is the subgroup functor whose `T`-points belong to the range
of every actual homomorphism `i : H ⟶ G` satisfying both `IsClosedSubgroup i` and
`ContainsCommutators (SubgroupFunctor.range i)`. Its membership lemma is
`mem_derivedSubgroup`. Subgroup closure and restriction stability follow from
those of each range. The identity `𝟙 G` is an admissible closed subgroup, as
`derivedSubgroup_total_admissible` proves using `SubgroupFunctor.range_id` and
`containsCommutators_top`.

The implemented elementary results are:

- `derivedSubgroup_containsCommutators`: every commutator lies in the intersection.
- `derivedSubgroup_le_range`: the intersection lies in every closed subgroup
  containing all commutators.
- `derivedSubgroup_isNormal`: conjugation preserves the intersection on every
  test scheme. The general helper `ContainsCommutators.isNormal` uses
  `g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h` and subgroup multiplication.

`IsDerivedSubgroup d`, for an actual `d : D ⟶ G`, means that `d` is a closed
subgroup and its entire range functor equals `derivedSubgroup G`.
`IsDerivedSubgroup.isRepresentedBy` supplies the published
`SubgroupFunctor.IsRepresentedBy` predicate, since a closed immersion is a
monomorphism. Its other elementary lemmas transfer commutator containment,
normality and minimality to that inclusion.

The intersection and representation predicate provide no chosen `D` or closed
inclusion. Closed representability over fields is a separate statement and
requires a substantive proof before such a choice is available. Likewise the
field base-change, smoothness, connectedness and commutative annihilation
properties are separate proof targets. In particular the elementary lemmas do
not establish faithfully flat local generation by commutators, which Milne
Corollary 6.19(c) uses to obtain the scalar-extension annihilation in (d).

Milne Remark 6.23, printed p.131 / PDF p.147, warns that `DG(k)` can differ from
the abstract commutator subgroup `D(G(k))`, for example for `PGL_n`. This module
asserts no equality between them, no rational-point quotient formula and no
surjectivity on rational points.

The retained official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`, was
checked. Its displayed Chapter 6 correction concerns Example 6.48. The HTML
contains a commented-out caution about 6.19(c)–(e), which is not a displayed
correction; it is not used to add a smoothness hypothesis here.
