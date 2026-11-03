# Split tori are split solvable over their ground field

Author: Worker 1295.

`Langlands.GroupScheme.SplitTorusSplitSolvableStatement.{u}` is the proposition
that every actual split torus over every field `k : Type u` satisfies the
unchanged public predicate `IsSplitSolvableGroupScheme`.

The Lean quantifiers range over every `T : GroupScheme (Spec k)`, with only
`IsSplitTorus T` as a mathematical hypothesis. In particular, the statement
includes finite and imperfect fields, every characteristic, and the torus of
rank zero. It does not assume that `T` has already been presented as a
commutative group scheme, or supply a normal-series witness as a premise.

## Meaning of the conclusion

The imported `IsSplitTorus` asserts an isomorphism of actual group schemes over
`Spec k` with a finite product of copies of the actual multiplicative group.
The imported `IsSplitSolvableGroupScheme` requires smoothness, an affine
structure morphism, connected underlying space, solvability in the published
algebraic-closure-point sense, and a finite `SplitSolvable.HasSeries` witness.

That series uses actual smooth connected closed normal subgroups and actual
represented fppf quotients. Each quotient is a one-dimensional vector group or
is isomorphic over `k` to Gm. The quotient condition includes flatness,
surjectivity and local finite presentation of the actual scheme morphism and
equality of its kernel with the specified subgroup functor on every relative
test scheme. Its zero case says that the represented group functor is trivial
on every test. None of these imported requirements is weakened or redefined.

## Sources and derivation

Milne, *Algebraic Groups* (2017), Definition 12.14 and the following paragraph,
printed p.236, one-based PDF p.252, describe split tori as finite products of
Gm over the ground field and as smooth connected diagonalizable groups.
Registered source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The registered errata snapshot dated 2026-11-02 has no correction to this
definition or paragraph.

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), the
beginning of Section B.1, printed p.561, one-based PDF p.587, defines splitting
for a smooth connected solvable group using a composition series with ground
field quotients Ga or GL₁, and identifies the torus case with the usual notion.
Registered source: `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

This proposition is a derived bridge between those two published interfaces.
Appendix B imposes positive characteristic as a standing convention, whereas
the bridge is stated in every characteristic: the proposed derivation is the
finite coordinate series of a product of Gm, which uses no characteristic
restriction. A proof must construct the actual subgroup inclusions and fppf
quotient morphisms, verify their properties, handle the empty product, and
transport the result along the given group-scheme isomorphism. It must also
supply the four outer structure properties. These are retained proof
obligations, not additional hypotheses or proof claims.

This module records only a proposition definition. It proves no split-solvable
adapter, fixed-point theorem, or conjugacy result. The intended consumer is the
split-solvable fixed-point route to rational containment of split tori in
pseudo-parabolic subgroups.
