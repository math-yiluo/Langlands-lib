# Existence of the ground-field solvable radical

Author: Worker 1378.

`Langlands.GroupScheme.SolvableRadicalExistenceStatement.{u}` is a
Prop-valued statement for every universe `u`. For every field `k : Type u`
and every actual group scheme `G` over `Spec (CommRingCat.of k)` with
`Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`,
it asks for an actual group scheme `R` over the same base and a
group-scheme morphism `r : R ⟶ G` satisfying the published
`IsSolvableRadical r`.

## The imported predicate

`IsSolvableRadical r`, in `Langlands.GroupScheme.Rational.LeviSubgroup`,
requires all of the following:

- `r` is a closed immersion (`IsClosedSubgroup r`);
- `R` is smooth over `k` and its underlying space is connected;
- `IsSolvableGroupScheme R` holds: the group of points over
  `AlgebraicClosure k` of the base change of `R` is solvable;
- the represented subgroup functor `SubgroupFunctor.range r` is normal on
  every test scheme;
- `r` is greatest: for every actual group scheme `H` over `k` and every
  closed subgroup morphism `h : H ⟶ G` with `H` smooth, connected and
  solvable and with normal range, `SubgroupFunctor.range h` is contained in
  `SubgroupFunctor.range r`.

Ranges, normality and containment are tested on all schemes over the base,
including nonaffine and nonreduced tests. The statement reuses this
predicate unchanged and adds the existence quantifiers that the predicate
alone does not supply.

This is the ground-field radical. The competitors in the greatestness
condition are the subgroups defined over `k`. The statement makes no
assertion about the base change of `R` to an algebraic closure, which in
general is not the radical of the base change of `G` over an imperfect
field. It places no perfectness, characteristic, algebraic-closure or
reductivity restriction on `k` or `G`, and it asserts no uniqueness.

## Source

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field* (Cambridge University Press, 2017),
registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Printed page `p` is PDF page `p + 16`.

- §6.44, printed p.135 (PDF p.151). For a connected group variety `G`
  over `k`, the radical `R(G)` is the largest connected solvable normal
  subgroup variety. The book's convention in that section is that
  algebraic groups are affine.
- Proposition 6.42, printed p.134 (PDF p.150), with Lemma 6.41, supplies
  the existence of the largest smooth connected normal subgroup with a
  property stable under extensions and quotients. Solvability has these
  properties by 6.27.

The translation into the Library predicates is the following. A connected
group variety over `k` is an actual smooth affine group scheme over
`Spec k` with connected underlying space. A subgroup variety is a smooth
closed subgroup morphism. Normality of an algebraic subgroup is normality
of its points for every `k`-algebra; here it is the all-test normality of
the range subgroup functor. Solvability is the published
`IsSolvableGroupScheme`, whose Markdown in `Absolute.Borel` explains its
agreement with Milne's Definition 6.26 for smooth groups. Largest means
that every competitor's range is contained in the range of `r`.

The pinned errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
contains no correction to §§6.41–6.44. The statement is derived from these
passages rather than a verbatim statement.

## Relation to other targets

This proposition is the solvable analogue of the published
`UnipotentRadicalExistenceStatement` in
`Reductive.UnipotentRadicalExistenceStatement`, with the same hypotheses
on `G`. Together with a base-change assertion for connected reductive
groups it gives `ReductiveGeometricSolvableRadicalExistsStatement`.

The file defines a proposition and supplies no proof or chosen radical.
