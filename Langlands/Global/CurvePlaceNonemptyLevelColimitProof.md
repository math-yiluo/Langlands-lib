# Colimits over nonempty finite sets of actual curve places

Authors: Worker 208 (Lean proof and first Markdown); Worker 840 (submission
and Markdown revision).

The theorem `Langlands.Global.curvePlaceNonemptyLevelColimit` has type
exactly `CurvePlaceNonemptyLevelColimitStatement.{u}`. The fields `k` and
`F` belong to an arbitrary common universe `u`, with `Algebra k F` and a
nonempty type of actual places `AlgebraicCurve.Place k F`. No other
hypothesis is added: no function-field, perfectness or separability
condition. The proof uses only published declarations, imported from
`CurvePlaceNonemptyLevel` (through the statement module),
`CurvePlaceAdeleLevelTopologyProof` and `FiniteAdeleLevelColimitProof`.

## Chosen place

Several steps fix one place `p`, obtained by `Classical.choice` from the
target's `Nonempty (AlgebraicCurve.Place k F)` instance. The published
monotone map `curvePlaceNonemptyLevelEnlarge k F p` sends a finite set `S`
to the nonempty set `insert p S`, and `curvePlaceNonemptyLevelEnlarge_le`
gives `S ⊆ insert p S`. Below, `E` denotes this map.

## Exhaustion and final topology

`exists_mem_curvePlaceNonemptyAdeleLevel` proves the first conjunct. The
published `exists_mem_curvePlaceAdeleLevel` puts each element `a` in the
level of some finite set `S`. Since levels are monotone
(`curvePlaceAdeleLevel_mono`), `a` also lies in the level of `E S`.

`continuous_iff_curvePlaceNonemptyAdeleLevel` proves the second conjunct
for every topological space `X` in universe `u`. One direction composes
`f` with the continuous subtype inclusion. For the converse, the proof
checks continuity of `f` at each point `a`. It takes a nonempty level
containing `a`. That level is open (`isOpen_curvePlaceAdeleLevel`), so its
inclusion is an open embedding. Continuity at `a` then follows from
continuity of the restriction at `⟨a, ha⟩`.

## The commutative-ring colimit

Let `c` be a cocone over `curvePlaceNonemptyAdeleLevelRingDiagram k F`.
The definition `curvePlaceNonemptyAdeleLevelRingDesc` applies the
published `SubringCover.desc`. Its index is the type of all finite sets of
places, and the subring at `S` is the level of `E S`. Its inputs are:

- monotonicity, from `E.monotone` and `curvePlaceAdeleLevel_mono`;
- the cover property, from all-finite exhaustion followed by enlargement;
- the family `S ↦ (c.ι.app (E S)).hom`;
- compatibility, from the cocone law `c.w` at the inclusion
  `E S ≤ E T`.

`curvePlaceNonemptyAdeleLevelRingDesc_apply` shows that the resulting
homomorphism agrees with `c.ι.app S` on the level of each original
nonempty `S`. By `SubringCover.desc_apply`, its value at `a` is the
component at `E S.val`, applied to `a` viewed in the larger level. The
cocone law `c.w` at the inclusion `S ≤ E S.val` identifies this value
with `(c.ι.app S) a`.

`curvePlaceNonemptyAdeleLevelRingIsColimit` takes `desc` to be this
homomorphism, made a morphism by `CommRingCat.ofHom`. The factorization
law `fac` is the formula above. For uniqueness, let `m` be any morphism
satisfying the factorization laws and let `a` be an element. Put `a` in
a nonempty level `S` by exhaustion. Both `m` and `desc` agree with
`c.ι.app S` at `a`, so they agree at `a`.

## The topological-ring colimit

Let `c` be a cocone over `curvePlaceNonemptyAdeleLevelDiagram k F` in
`TopCommRingCat`. In `curvePlaceNonemptyAdeleLevelIsColimit`, `desc` is
the ring homomorphism `f` built above from the cocone obtained by
forgetting topology, `(forget₂ TopCommRingCat CommRingCat).mapCocone c`.
By the factorization formula, the restriction of `f` to each nonempty
level equals the underlying function of the continuous leg `c.ι.app S`.
The continuity criterion above therefore shows that `f` is continuous.
The laws `fac` and `uniq` follow from the factorization formula and
exhaustion, as in the ring case.

## Packaging

`curvePlaceNonemptyLevelColimit` introduces `k`, `F` and their instances,
and returns the four conjuncts of the target in order:

1. exhaustion;
2. the final-topology criterion;
3. `Nonempty (IsColimit (curvePlaceNonemptyAdeleLevelCocone k F))`;
4. `Nonempty (IsColimit (curvePlaceNonemptyAdeleLevelRingCocone k F))`.

## Scope and source

The statement is derived infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Section 2,
printed p.1. There, finite nonempty place sets index the open adelic
levels and their direct limit. This proof concerns only the published
actual curve-place rings, topologies, literal inclusions and canonical
cocones. Three topics remain separate obligations of the whole-paper
task:

- identification with the conventional places of a global function field;
- local compactness;
- comparisons of geometric point spaces.
