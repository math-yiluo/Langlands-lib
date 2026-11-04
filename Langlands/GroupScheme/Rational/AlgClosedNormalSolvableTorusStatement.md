# Normal solvable subgroups of reductive groups over algebraically closed fields

Author: Worker 1378.

`AlgClosedReductiveNormalSolvableTorusStatement.{u}` is a proposition
target over every algebraically closed field `k : Type u`. Let `G` be an
actual group scheme over `Spec k` with `IsPseudoReductive G`. Let
`h : H → G` be a closed subgroup morphism. Suppose `H` is smooth, has
connected underlying space and is solvable, and the range of `h` is
normal. The target asserts that `H` is a torus and that `h` is central.

## Quantifiers and predicates

- `k` ranges over all fields in universe `u` with `[IsAlgClosed k]`,
  and `S = Spec k`.
- `G` ranges over the published `GroupScheme S`. The published
  predicate `IsPseudoReductive G` in `Reductive.Basic` states that `G`
  is smooth, affine and connected over `k`, and that
  `HasTrivialUnipotentRadical G` holds. The latter means that every
  closed subgroup morphism `i : U → G` with `U` smooth, connected,
  unipotent (`IsUnipotent U`) and of normal range has trivial range
  functor. Over an algebraically closed field this is the notion of a
  connected reductive group, as the docstring of `IsPseudoReductive`
  records.
- `H` ranges over `GroupScheme S` and `h` over group-scheme morphisms
  `H ⟶ G`. The hypotheses are:
  - `IsClosedSubgroup h`, meaning the underlying scheme map is a
    closed immersion;
  - `Smooth H.X.hom` and `ConnectedSpace H.X.left`;
  - `IsSolvableGroupScheme H`, meaning the group of algebraic-closure
    points of the base change of `H` is solvable;
  - `(SubgroupFunctor.range h).IsNormal`, normality of the range
    subgroup functor on every test scheme over `S`.
- The conclusion has two parts:
  - `IsTorus H` is the published torus predicate in `Torus.Lattice`:
    some field extension `K` of `k` in universe `u` splits the base
    change of `H`.
  - `IsCentral h` is the published predicate in `Rational.Characters`:
    for every test scheme `T` over `S`, every `T`-point of `H` maps into
    the centre of `G` at `T`.

The hypotheses are exactly the competitor conditions in the published
`IsSolvableRadical` greatestness field. Algebraic closedness is part of
the hypothesis: over an imperfect field a pseudo-reductive group may have
non-toral radical, so the target is not asserted there.

## Source and derivation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (Cambridge University Press, 2017),
registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Printed page `p` is PDF page `p + 16`. The relevant passages are:

- Corollary 17.62(b) and its proof, printed p.372 (PDF p.388). For a
  reductive group `G`, `R(G) = Z(G)^t`. The proof shows that
  `R(G_{k^a})` is a torus because `R_u(G_{k^a}) = e`, and then uses
  rigidity (12.37) to show that `G` acts trivially on `R(G)` by inner
  automorphisms, so that `R(G)` is central.
- Theorem 16.33(a)–(c), printed pp.335–336 (PDF pp.351–352). For a
  smooth connected solvable group `H` over a perfect field, there is a
  normal unipotent subgroup `H_u` containing every unipotent algebraic
  subgroup of `H`. It is smooth and connected, and `H/H_u` is a torus.
- Corollary 12.38, printed p.244 (PDF p.260). A normal subgroup of
  multiplicative type in a connected algebraic group is central. It is
  proved from rigidity, Corollary 12.37 on the same page.
- §6.44 and §6.46, printed p.135 (PDF p.151). They define the radical
  `R(G)` as the largest connected solvable normal subgroup variety and
  reductivity by triviality of `R_u(G_{k^a})`.

The target is the following derived form of the proof of 17.62(b) over
`k = k^a`, stated for an arbitrary competitor `H` rather than for
`R(G)` itself. Since `H_u` contains every unipotent subgroup of `H`, it
is stable under the conjugation action of `G` on the normal subgroup
`H`. Thus `H_u` is a smooth connected unipotent normal subgroup of `G`,
and it is trivial because `R_u(G) = e`. By 16.33(c) the group
`H = H/H_u` is a torus. By 12.38 a normal torus of the connected group
`G` is central.

The translation into the Library predicates follows the conventions of
the published `IsSolvableRadical` and `HasTrivialUnipotentRadical`:

- subgroup varieties are smooth closed subgroup morphisms;
- normality is all-test normality of the range subgroup functor;
- solvability is `IsSolvableGroupScheme`; over an algebraically closed
  field it is solvability of the group of `k`-points of `H`, the
  convention of 16.34(c),(d), printed p.336 (PDF p.352);
- centrality of the subgroup `H` in Milne's sense, i.e. `H ⊂ Z(G)`,
  is the all-test predicate `IsCentral h`.

The official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`
contains no correction to these passages. The target is derived from
them rather than a verbatim statement.

## Relation to other targets

This proposition supplies the torus and centre half of Corollary
17.62(b) over the algebraic closure. Together with
`SolvableRadicalExistenceStatement` and
`ReductiveLargestCentralSubtorusBaseChangeStatement`, it is used to
prove `ReductiveGeometricSolvableRadicalExistsStatement`. The base change
of a connected reductive group to its algebraic closure satisfies
`IsPseudoReductive`, so the target applies there without any separate
field-extension result for reductivity.

The file imports only `Rational.LeviSubgroup` and defines only a
proposition target. It proves no structure theorem.
