# Two remarks of Chapter VII (Renard VII.2.6 and VII.3.1): statements

Module `Langlands.Representation.Exponents.TemperedBruhatRemarksStatements`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. The module contains two
**statements**, both `Prop`-valued definitions; it proves nothing:

- `TemperedReducibleNotUnitarizableStatement` (universes `u, v`);
- `BruhatIdentityExtremesStatement` (universe `u`).

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The two remarks are short unheaded or
headed-remark assertions with no Library statement. They are grouped as one unit.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VII.2.6, printed pp.231–232 / PDF pp.237–238, and VII.3.1, printed
pp.232–233 / PDF pp.238–239.

VII.2.6, after the Corollary "Une représentation irréductible tempérée est unitaire":

> *Remarque.* Sans l'hypothèse d'irréductibilité dans le corollaire précédent, la
> conclusion de celui-ci peut être fausse.

VII.3.1, after the Definition of the Bruhat order `w̄ ≤_{PQ} w̄'` if `P w̄ Q ⊂ closure(P w̄' Q)`
on `W_M \ W_G / W_M ≃ P \ G / Q`, and the choice of a total order `⪯` refining it:

> Ainsi, si `P = Q`, `1̄` est le plus petit élément pour l'ordre `⪯`. Au contraire, si
> `Q = P̄`, c'est le plus grand.

The published statement of the Corollary is `TemperedIrreducibleUnitarizableStatement`;
the published Bruhat relation is `Langlands.Geometric.BruhatLE`, with refinements
`Langlands.Geometric.IsBruhatRefinement`.

## The statements

Both use the represented setting of the published Chapter VII statements: a
nonarchimedean local field `k` with `T2Space`, a connected reductive group scheme `G`
over `k`, the canonical topology `RationalPointFamily.pointTopology` on `G(k)`, and the
`LocallyCompactSpace` and `NonarchimedeanGroup` binders.

`TemperedReducibleNotUnitarizableStatement`: for every such `k` there are a connected
reductive `G` and a smooth complex representation `π` of `G(k)`, on a carrier in
`Type v`, such that `IsNormalizedExponentTempered hG π` (the published temperedness
predicate, which includes admissibility) holds and `IsUnitarizable π.representation`
(existence of an invariant positive definite hermitian form) fails.

`BruhatIdentityExtremesStatement`: for every parabolic `p : P ⟶ G`:

1. for every `w ∈ P(k) \ G(k) / P(k)`, `BruhatLE (pointImage p) (pointImage p) 1̄ w`,
   that is `P(k) ⊆ closure(P(k) w P(k))`;
2. for every parabolic `q : Q ⟶ G` such that `M` is a rational Levi subgroup of both
   (`l : M ⟶ P`, `lQ : M ⟶ Q`, `lQ ≫ q = l ≫ p`) and `P(k) ∩ Q(k) = M(k)`, and for every
   `w ∈ P(k) \ G(k) / Q(k)`, `BruhatLE (pointImage p) (pointImage q) w 1̄`, that is
   `P(k) w Q(k) ⊆ closure(P(k) Q(k))`.

## Formalization choices

- **"Peut être fausse".** The remark says the conclusion can fail for some reducible
  tempered representation. The statement asserts, for every `k`, one connected reductive
  `G` and one tempered representation that is not unitarizable. Renard gives no example.
  One example is `G = 𝔾_m` and the two-dimensional representation
  `x ↦ [[1, v(x)], [0, 1]]`, where `v` is the valuation. Its only generalized exponent is
  the trivial character, so it is tempered. It is a non-split extension of the trivial
  character by itself, and an invariant positive form would split it. The example is
  explanation only; the statement does not fix `G`.
- **Least and greatest for `⪯`.** The statement gives the Bruhat form: `1̄` is below every
  element when `Q = P`, and above every element when `Q = P̄`. Renard's claim for the
  chosen refinement `⪯` follows, because a refinement preserves the relation
  (`IsBruhatRefinement`). The Bruhat form is the geometric content.
- **`Q = P̄`.** As in the published VI.9.6 and VII.4.1 statements, the opposite parabolic
  is any parabolic with the same rational Levi `M` and `P(k) ∩ Q(k) = M(k)`.
- **`P = Q`.** The first clause needs only a parabolic `p`. The Levi map `l` is a binder
  of the whole statement because the second clause uses it.

## Why the statements are true

The proofs are separate obligations.

- VII.2.6 Remark: the `𝔾_m` example above. Admissibility holds because the carrier is
  finite-dimensional. Smoothness holds because `v` vanishes on the units. For `G = 𝔾_m`
  the only parabolic is `G`, so temperedness reduces to the real part of the trivial
  exponent, which is `0`.
- VII.3.1, `P = Q`: by the Bruhat decomposition and its closure relations (Borel–Tits),
  the closure of `P(k) w P(k)` is a union of double cosets containing the closed cell
  `P(k)`.
- VII.3.1, `Q = P̄`: `P(k) P̄(k)` is the open dense big cell, so its closure is `G(k)`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Exponents.ArbitraryParabolicTempered` | `IsNormalizedExponentTempered` |
| `Langlands.Representation.Unitary.Basic` | `IsUnitarizable` |
| `Langlands.Representation.Intertwining.PQRegularity` | `Geometric.BruhatLE`, `parabolicDoubleCosets`, `identityParabolicDoubleCoset`, `pointImage` (through its imports) |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
