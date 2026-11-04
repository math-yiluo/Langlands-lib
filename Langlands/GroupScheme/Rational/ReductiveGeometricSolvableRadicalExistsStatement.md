# Geometric solvable radicals of connected reductive groups

Author: Worker 1378.

`ReductiveGeometricSolvableRadicalExistsStatement.{u}` is a proposition
target over every field `k : Type u`. Given an actual group scheme `G`
over `Spec k` with `IsConnectedReductive G`, it asserts the existence of
an actual group scheme `R` over `Spec k` and a group-scheme morphism
`r : R → G` satisfying the published predicate
`IsGeometricSolvableRadical r`.

The target has no assumption that `k` is perfect, that `G` is split, or
that a maximal torus has been supplied. It asserts existence and makes
no choice of a representative.

## Quantifiers and predicates

- `k` ranges over all fields in universe `u`, with `S = Spec k`.
- `G` ranges over the published `GroupScheme S`.
- `IsConnectedReductive G` is the published predicate in
  `Reductive.Basic`: `G` is smooth, affine and connected over `k`, and
  the base change of `G` to `AlgebraicClosure k` has trivial unipotent
  radical. This is the geometric notion of a connected reductive group.
- The conclusion supplies `R : GroupScheme S` and `r : R ⟶ G`.

The imported predicate `IsGeometricSolvableRadical r` in
`Rational.LeviSubgroup` is the conjunction of `IsSolvableRadical r` and
`IsSolvableRadical` of the base-changed morphism
`(GroupScheme.baseChange (toAlgebraicClosure k)).map r`.
For a morphism `r : R → G` over a field, `IsSolvableRadical r`
requires all of the following:

- `r` is a closed immersion (`IsClosedSubgroup r`);
- `R` is smooth and its underlying space is connected;
- `IsSolvableGroupScheme R` holds, that is, the group of
  algebraic-closure points of the base change of `R` is solvable;
- the represented subgroup functor `SubgroupFunctor.range r` is normal
  on every test scheme;
- `r` is greatest: for every actual group scheme `H` and every
  closed subgroup morphism `h : H → G` with `H` smooth, connected and
  solvable, and with normal range, the range functor of `h` is
  contained in that of `r` on every test scheme.

For the base-changed morphism these conditions are read over
`AlgebraicClosure k`, using that field's own algebraic-closure point
convention for solvability. Greatestness over the algebraic closure
quantifies over all smooth connected solvable normal closed subgroups
of the base change of `G`. These need not be defined over `k`. Thus the
second conjunct is the descent assertion: the geometric radical is the
base change of the ground-field radical.

The statement does not assert that `R` is a torus, that `r` is central,
or any comparison with `IsLargestCentralSubtorus`. It also asserts no
uniqueness.

## Source and derivation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (Cambridge University Press, 2017),
registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Printed page `p` is PDF page `p + 16`. The relevant passages are:

- §6.44, printed p.135 (PDF p.151). For a connected group variety `G`
  over `k`, the radical `R(G)` is the largest connected solvable normal
  subgroup variety. Its existence is Proposition 6.42.
- §6.46, printed p.135 (PDF p.151). A connected group variety over `k`
  is reductive if its geometric unipotent radical `R_u(G_{k^a})` is
  trivial.
- Corollary 17.62(b),(c), printed pp.372–373 (PDF pp.388–389). For a
  reductive group `G`, (b) states `R(G) = Z(G)^t`, the largest subtorus
  of the centre. Part (c) states that the formation of `R(G)` commutes
  with extension of the base field.

The ground-field conjunct is Milne's radical `R(G)` of §6.44. The
algebraic-closure conjunct is Corollary 17.62(c) for the extension
`k → AlgebraicClosure k`: the base change of `R(G)` is `R(G_{k^a})`.
The official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
contains no correction to §§6.42–6.46 or 17.61–17.62.

The translation into the Library predicates is the following:

- A subgroup variety is a smooth algebraic subgroup, here a smooth
  closed subgroup morphism.
- Normality of an algebraic subgroup is normality of its points for
  every `k`-algebra. Here it is the all-test normality of the range
  subgroup functor.
- Solvability is the published `IsSolvableGroupScheme`. Its Markdown in
  `Absolute.Borel` explains the agreement with Milne's Definition 6.26
  for smooth groups.

Milne's proof of 17.62(b) identifies `R(G)` with a central torus, using
17.61 and rigidity (12.37). Part (c) then follows because the formation
of the centre and of its largest subtorus commutes with field extension.
This target records only the radical assertions (§6.44 and 17.62(c)),
not the torus and centre identification of 17.62(b). It is derived
from these passages rather than a verbatim statement.

## Relation to other targets

This proposition is the connected reductive case of the descent needed
for `ParabolicGeometricSolvableRadicalExistsStatement` in
`Rational.ParabolicGeometricSolvableRadicalExistsStatement`. There the
radical of a rational parabolic `P` is to be built as the inverse image
of the radical of a Levi quotient. It shares that target's predicates
and conventions, and imports only `Rational.LeviSubgroup`.

The file defines only a proposition target. It proves no existence or
descent theorem.
