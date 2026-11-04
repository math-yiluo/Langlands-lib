# Largest central subtori of reductive groups under field extension

Author: Worker 1378.

`ReductiveLargestCentralSubtorusBaseChangeStatement.{u}` is a proposition
target over every field `k : Type u` and every field extension `K` of
`k` in the same universe. Let `G` be an actual group scheme over
`Spec k` with `IsConnectedReductive G`. Let `Z` be an actual commutative
group scheme over `Spec k`, and let `z : Z → G` be a homomorphism with
`IsLargestCentralSubtorus z`. The target asserts that the base change of
`z` along `Spec K → Spec k` is again a largest central subtorus of the
base change of `G`.

## Quantifiers and predicates

- `k` and `K` range over all fields in universe `u`, with an arbitrary
  `Algebra k K` structure. The base-change morphism is
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`. No separability,
  finiteness or algebraic-closedness assumption is made.
- `G` ranges over the published `GroupScheme (Spec k)`. The published
  predicate `IsConnectedReductive G` in `Reductive.Basic` states that
  `G` is smooth, affine and connected, and that the base change of `G` to
  `AlgebraicClosure k` has trivial unipotent radical.
- `Z` ranges over the published `CommGroupScheme (Spec k)`, and `z` over
  group-scheme morphisms `Z.toGrp ⟶ G`.
- The published predicate `IsLargestCentralSubtorus z` in
  `Rational.LeviSubgroup` states:
  - `Z.toGrp` is a torus (`IsTorus`);
  - `z` is a closed immersion (`IsClosedSubgroup z`);
  - `z` is central (`IsCentral z`), meaning every point of `Z` on every
    test scheme maps into the centre of `G`;
  - `z` is greatest: for every actual commutative group scheme `A` and
    every closed central morphism `a : A.toGrp → G` with `A.toGrp` a
    torus, the range functor of `a` is contained in that of `z` on every
    test scheme.
- The conclusion is the same predicate over `K`. Its source is the
  commutative group scheme `(CommGroupScheme.baseChange _).obj Z`, and
  its morphism is `(GroupScheme.baseChange _).map z` into the base
  change of `G`. The underlying group scheme of the base change of `Z`
  is the base change of `Z.toGrp` by definition.

Greatestness over `K` quantifies over all closed central tori of the
base change of `G`. These need not be defined over `k`. Thus the target
asserts descent for the largest central subtorus, not only stability of
the torus, closedness and centrality under base change.

## Source and derivation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group
Schemes of Finite Type over a Field* (Cambridge University Press, 2017),
registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Printed page `p` is PDF page `p + 16`. The relevant passages are:

- Corollary 17.62(a)–(c) and its proof, printed pp.372–373 (PDF
  pp.388–389). For a reductive group `G`: (a) the centre `Z(G)` is of
  multiplicative type; (b) `R(G) = Z(G)^t`, the largest subtorus of
  `Z(G)`; (c) the formation of `R(G)` commutes with extension of the base
  field. The proof of (c) states that "the formation of the centre, and
  the largest subtorus, commute with extension of the base field".
- Notation 12.29, printed p.241 (PDF p.257). For a group `H` of
  multiplicative type, `H^t` is the largest subtorus of `H`. It is the
  unique subtorus `T` of `H` with `H/T` finite, so its formation commutes
  with extension of the base field.
- §6.46, printed p.135 (PDF p.151). A connected group variety over `k`
  is reductive if `R_u(G_{k^a})` is trivial.

The target is derived from these passages as follows. Over `k`, a
largest central subtorus `z` is `Z(G)^t`: every subtorus of `Z(G)` is a
central torus, hence lies in `z`, and `z` lies in `Z(G)` and is a torus,
hence lies in `Z(G)^t`. The centre commutes with base change, so
`Z(G_K) = Z(G)_K`, which is of multiplicative type by 17.62(a). By 12.29,
`(Z(G)^t)_K = (Z(G)_K)^t`. Every closed central torus of `G_K` is a
subtorus of `Z(G_K)` and therefore lies in `(Z(G)^t)_K`, the base change
of `z`.

The translation into the Library predicates is the following:

- a subtorus of the centre is a closed central torus, recorded by
  `IsTorus`, `IsClosedSubgroup` and `IsCentral`;
- containment of algebraic subgroups is containment of range subgroup
  functors on every test scheme over the field.

The target asserts only the largest-central-subtorus property after base
change. It does not assert that the centre is of multiplicative type,
that `z` is the radical, or any uniqueness. The official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` contains no correction
to 12.29 or 17.61–17.62. The target is derived from these passages
rather than a verbatim statement.

## Relation to other targets

This proposition is the field-extension part of Corollary 17.62(c).
Together with `SolvableRadicalExistenceStatement` and
`AlgClosedReductiveNormalSolvableTorusStatement`, it is used to prove
`ReductiveGeometricSolvableRadicalExistsStatement` with
`K = AlgebraicClosure k`.

The file imports only `Rational.LeviSubgroup` and defines only a
proposition target. It proves no base-change theorem.
