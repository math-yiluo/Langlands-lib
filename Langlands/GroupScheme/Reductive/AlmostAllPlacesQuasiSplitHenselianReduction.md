# Almost all places quasi-split, from henselian quasi-splitness

Worker 62 and Worker 648.

This module states and proves that the published, not yet proved,
[`HenselianFiniteResidueQuasiSplitStatement`](../RelativeLevi/HenselianQuasiSplitStatement.md)
implies the published
[`AlmostAllPlacesQuasiSplitStatement`](AlmostAllPlacesQuasiSplitStatement.md), for every universe
`u`. It adds no axioms. It does not prove `AlmostAllPlacesQuasiSplitStatement` unconditionally,
because its hypothesis is still open.

## Statement

`Langlands.GroupScheme.AlmostAllPlacesQuasiSplitHenselianReductionStatement.{u} : Prop` is the
implication

`HenselianFiniteResidueQuasiSplitStatement.{u} → AlmostAllPlacesQuasiSplitStatement.{u}`.

The hypothesis says that a reductive group scheme (`IsReductive`) over the spectrum of a
henselian local ring with finite residue field is quasi-split over the base
(`IsRelativeQuasiSplit`: it has a Borel subgroup over the base). It also gives a splitting
over a finite étale local extension, which this module does not use. The conclusion says
that for every number field `F : Type u` and every group scheme `G` over `Spec F` with
`IsConnectedReductive G`:

1. for all but finitely many `v : FinitePlace F`, the base change of `G` to the completion
   `FiniteCompletion F v` satisfies `IsQuasiSplit`;
2. for every object `X` of `Over (Spec F)` with a `ModObj G.X X` action whose structure map is
   flat, surjective and quasi-compact, and whose shear map `ModObj.leftSMul G.X X` is an
   isomorphism, `X` has a point over `FiniteCompletion F v` (`RingPoint F X …`) for all but
   finitely many `v : FinitePlace F`.

## Theorems

- `almostAllPlacesQuasiSplit_of_henselian hH : AlmostAllPlacesQuasiSplitStatement.{u}`, for
  `hH : HenselianFiniteResidueQuasiSplitStatement.{u}`.
- `almostAllPlacesQuasiSplitHenselianReduction :
  AlmostAllPlacesQuasiSplitHenselianReductionStatement.{u}`. This is the previous theorem.

## Proof

The two clauses are proved separately by published theorems, and the proof combines them.

1. Clause 1 is `almostAllPlacesQuasiSplitClauseReduction hH F G hG`, from the published
   module [`AlmostAllPlacesQuasiSplitClauseReduction`](AlmostAllPlacesQuasiSplitClauseReduction.md)
   (Worker 62). Its conclusion is word for word the first conjunct of the target. That proof
   spreads `G` out to a reductive model over a ring of `S`-integers, base changes it to the
   completed integers `𝒪_{F_v}` for `v ∉ S`, applies `hH` there to get a Borel subgroup over
   `𝒪_{F_v}`, and restricts that subgroup to the generic fibre.
2. Clause 2 is
   `AlmostAllPlacesTorsorPoints.eventually_nonempty_ringPoint_of_torsor F G hG X hfl hs hqc hiso`,
   from the published module [`AlmostAllPlacesTorsorPoints`](AlmostAllPlacesTorsorPoints.md)
   (Worker 648). It does not use `hH`. Its hypotheses and conclusion are word for word the
   second conjunct of the target. That proof shows the torsor is smooth, separated,
   quasi-compact and geometrically connected over `F`. It then applies the published theorem
   `Langlands.Global.eventually_nonempty_ringPoint_of_smooth_geometricallyConnected`, which
   uses uniform Lang–Weil bounds and spreading out.

## Provenance

The target is Conrad, *Reductive group schemes* (2014), Exercise 5.5.3(iii), printed
pp.182–183 (registered as `conrad-2014-reductive-group-schemes`), for number fields. The
hypothesis is the henselian form of part (ii) of that exercise. This module is an internal
reduction for Task 6635 (proof of `AlmostAllPlacesQuasiSplitStatement`). When a proof of
`HenselianFiniteResidueQuasiSplitStatement` is published, applying
`almostAllPlacesQuasiSplit_of_henselian` to it proves the target.
