# Almost-simplicity over a separably closed field is absolute

Author: Worker 166.

`Langlands.GroupScheme.SeparablyClosedAlmostSimpleAbsoluteStatement.{u}`
asserts that for every separably closed field `k : Type u` and every group
scheme `G` over `Spec k`, `IsAlmostSimple G` implies
`IsAbsolutelyAlmostSimple G`. This is a closed proposition definition. It
asserts no proof, chosen group, factorization or descent data.

The source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, Corollary 24.2 and its proof, printed p.512 /
PDF p.528. The preceding Proposition 24.1 identifies almost-simplicity of
a split semisimple group with indecomposability of its root system and
with geometric almost-simplicity. Corollary 24.2 applies because reductive
groups over separably closed fields are split. The proposition is the
geometric-factor input used in the discussion preceding Theorem 24.3,
printed p.513 / PDF p.529, and in the decomposition underlying CGP,
*Pseudo-reductive groups*, second edition, Proposition A.5.14.

The definitions are the published Library predicates. In particular,
`IsAlmostSimple` uses semisimplicity, noncommutativity and the condition on
smooth connected normal closed subgroups in Milne's official correction
to Definition 19.7. The registered 2017 errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read in full; its p.399
entry supplies that correction. The reversed parenthetical order in the
printed geometric clause is interpreted consistently with the
almost-simple branch, as explained in `AbsolutelyAlmostSimple.md`.
The errata contain no correction to Corollary 24.2.

There is no characteristic, perfectness, affine-morphism, topology or
simple-connectedness premise. The semisimple part of `IsAlmostSimple`
already supplies the affine finite-type smooth connected reductive
setting. Separably closed imperfect fields are included. The conclusion
is the published conjunction of ground-field almost-simplicity and
almost-simplicity after the actual base change to `AlgebraicClosure k`.
No claim about inseparable normal subgroup descent or arbitrary field
extension has been added.
