# Statement: simply connected central covers of split semisimple groups

Authors: Worker 1391 (original draft), Worker 1466 (source verification and preparation),
Worker 1457 (source and interface verification, final preparation).

This module states that every semisimple group scheme with a split maximal
torus, over an arbitrary field, is the target of a central isogeny from a
simply connected group. It defines one unproved proposition,
`Langlands.GroupScheme.SplitSimplyConnectedCoverExistenceStatement`, a
`Prop`-valued `def` with one universe parameter `u`, and proves nothing.

## Lean statement

```lean
def SplitSimplyConnectedCoverExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G → IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G),
        IsSimplyConnected C ∧ IsCentralIsogeny π
```

The module imports `Langlands.GroupScheme.SimplyConnected.Basic` and
`Langlands.GroupScheme.Torus.Maximal`, and reuses by name the Library
declarations `GroupScheme`, `CommGroupScheme`, `IsSemisimple`, `IsSplitTorus`,
`IsMaximalTorus`, `IsSimplyConnected` and `IsCentralIsogeny`.

## Quantifiers and meaning

- `k : Type u` is an arbitrary field in an arbitrary universe `u`; imperfect
  fields of positive characteristic are included.
- `G` is an actual group scheme over `Spec k` with `IsSemisimple G`: smooth,
  affine, connected, with trivial geometric unipotent radical, and with finite
  full scheme-theoretic centre.
- `T` is a commutative group scheme with `IsSplitTorus T.toGrp` (isomorphic to
  a finite product of copies of `Gm`), and `i : T.toGrp ⟶ G` is an actual
  homomorphism with `IsMaximalTorus i`. This predicate requires a closed torus
  inclusion maximal among closed torus inclusions: every factorization through
  another closed torus inclusion has an isomorphism as its torus map. Thus
  `(G, T)` is a split semisimple group in Milne's sense. The torus is only a hypothesis; it does not appear in the conclusion.
- The conclusion supplies an actual group scheme `C` over `Spec k` and an
  actual homomorphism `π : C ⟶ G` such that
  - `IsSimplyConnected C`: `C` is semisimple and every central isogeny onto
    `C` from a semisimple group scheme is an isomorphism;
  - `IsCentralIsogeny π`: the morphism underlying `π` is finite, flat,
    surjective and locally of finite presentation, and its full
    scheme-theoretic kernel (on all test schemes, nonreduced ones included) is
    central. The kernel may be nonreduced, for example `μ_p` in characteristic
    `p`.

No cover, factorization law, lifting or base-change property is assumed.

## Relation to the published target

The published proposition `SimplyConnectedCoverExistenceStatement`
(`SimplyConnected/CoverExistenceStatement`) asks, for every semisimple `G`, for
`π : C ⟶ G` with `IsSimplyConnectedCover π`, whose fields are `IsSemisimple G`,
`IsSimplyConnected C`, `IsCentralIsogeny π` and the unique-factorization law
`HasCentralCoverUniversalProperty π`. The present proposition is weaker in two
ways: `G` must have a split maximal torus, and the factorization law is not
part of the conclusion. It is the split input to the route of Milne,
Remark 23.60: construct the cover where `G` splits and descend it to `k`. The
factorization law is the subject of the separate statement
`SimplyConnectedCentralCoverUniversalProperty`
(`SimplyConnected/UniversalPropertyStatement`; originating statement task
`2be094ba-099b-4960-b5e3-3326c4320317`); a proof of the present proposition
must not use it, nor the published target.

## Sources and provenance

Provenance: source, split case.

- Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - Remark 23.60 (printed p.502, PDF p.518) constructs a universal cover of a
    split semisimple group from the inclusion of its character lattice `X`
    into the weight lattice `P(Φ)`. The Existence and Isogeny Theorems turn
    this root-datum isogeny into a central group isogeny with simply connected
    source. Restricting the remark to split groups and retaining just
    existence gives the present proposition over every field `k`.
  - Proposition 19.10 (printed p.400, PDF p.416) identifies semisimplicity
    among connected reductive groups with finiteness of the centre, matching
    the Library's `IsSemisimple`.
  - Definitions 18.5 and 18.7 (printed pp.388-389, PDF pp.404-405) define
    universal coverings through multiplicative isogenies; Proposition 19.15
    (statement printed p.400, PDF p.416; proof printed p.401, PDF p.417) shows
    that for semisimple groups this is the Library's `IsSimplyConnected` (central isogenies from semisimple groups
    are isomorphisms). The comparison is explained in
    `SimplyConnected/CoverExistenceStatement.md`.
- Milne's official errata, snapshot of 2026-11-02, source
  `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
  `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`. It lists
  no correction to Remark 23.60 or to the results cited below.

## Intended proof route (not part of the statement)

For a split semisimple `(G, T, i)` with root datum `P` on `(X, Y)`, given by
the published `RootDatumExistenceStatement` together with `P.IsReduced`:

1. `SplitSemisimpleRootDatumStatement` (Milne 21.48): the coroot lattice
   `Y_sc = P.corootSpan ℤ` has finite index in `Y`; dually `X` embeds in
   `X_sc = Hom(Y_sc, ℤ)`, the weight lattice `P(Φ)`.
2. The roots and coroots of `P` form a reduced root datum `P_sc` on
   `(X_sc, Y_sc)`; restriction `X → X_sc` and inclusion `Y_sc → Y` form a
   `RootPairing.Hom P P_sc` with injective weight and coweight maps.
3. `SplitReductiveExistenceStatement` (Milne 23.55) gives a split connected
   reductive `(C, T_C)` with root datum isomorphic to `P_sc`.
4. `SplitCentralIsogenyExistenceStatement` (Milne 23.9, 23.5) gives a central
   isogeny `π : C ⟶ G`.
5. `SplitSemisimpleRootDatumStatement` shows that `C` is semisimple, since its
   coroots span `Y(T_C)`. The sufficiency criterion
   `SplitCorootSpanSimplyConnectedStatement` in
   `SimplyConnected/SplitCriterionStatement` then shows that `C` is simply
   connected. Its source is Milne Proposition 23.29 (printed p.493,
   PDF p.509), expressed using coroot generation instead of equality of the
   character lattice with the weight lattice.

The three split statements are in `Reductive/SplitClassificationStatement`.
That sufficiency criterion must be proved without the present proposition.
