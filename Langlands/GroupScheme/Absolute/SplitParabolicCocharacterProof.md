# Split parabolics containing a fixed maximal torus: proof

Authors: Worker 3971 and Worker 4153. The reduction applied here is by
Worker 1358, and the three structural proofs are by the authors named in their
own Markdown files. The identical composition originally included as
`splitParabolicCocharacter` in `ParabolicDynamicForward` is consolidated here;
that module imports this proof under its canonical name below.

`Langlands.GroupScheme.splitParabolicCocharacterStatement.{u}` proves exactly the
unchanged published proposition
`Langlands.GroupScheme.SplitParabolicCocharacterStatement.{u}`
(`Langlands.GroupScheme.Absolute.SplitParabolicCocharacterStatement`).
The theorem has no hypotheses. Over every field `k : Type u`, let `G` be
connected reductive, let `j : T.toGrp ⟶ G` be a maximal torus with `T`
split, and let `i : P ⟶ G` be a geometric parabolic. For every
`f : T.toGrp ⟶ P` with `f ≫ i = j`, the theorem gives an actual
`nu : cocharacterLattice T` with

```
SubgroupFunctor.range i =
  Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ j).
```

This is an equality of subgroup functors, so it holds on every test scheme
over `Spec k`, including nonaffine and nonreduced tests. The cocharacter is
a cocharacter of the specified torus `T` over the original field `k`.

## Implemented proof

The proof is a single application of the published conditional reduction
`splitParabolicCocharacterStatement_of_absoluteBorelOvergroup`
(`Langlands.GroupScheme.Absolute.SplitParabolicCocharacterAbsoluteReduction`).
That theorem proves `SplitParabolicCocharacterStatement.{u}` from exactly
three premises, all at universe `u`. Each premise is discharged by a proved
Library theorem, so no premise remains:

1. `BorelConjugacyStatement.{u}`, discharged by `borelConjugacy`
   (`Langlands.GroupScheme.Absolute.BorelConjugacyProof`). This is Borel
   existence and conjugacy by a rational point. It covers every smooth affine
   group scheme with connected underlying space over an algebraically closed
   field of universe `u`, with no reductivity or characteristic assumption.
2. `AbsoluteBorelOvergroupCocharacterStatement.{u}`, discharged by
   `absoluteBorelOvergroupCocharacter`
   (`Langlands.GroupScheme.Absolute.BorelOvergroupCocharacterProof`).
   The field `k` is algebraically closed, `G` is connected reductive and `T`
   is split. Let `i : P ⟶ G` be a smooth closed subgroup, and let
   `b : B ⟶ P` satisfy `IsBorelPair (b ≫ i) j`. Then an actual
   `ζ : cocharacterLattice T` exists such that the field points of the
   range of `i` equal the field points of
   `Dynamic.parabolic (groupHom ζ ≫ j)`. That proof builds `ζ` as an integral
   Weyl-orbit sum of a regular cocharacter. It recognizes the overgroup from
   its root support.
3. `MaximalTorusBaseChangeStatement.{u}`, discharged by
   `maximalTorusBaseChange`
   (`Langlands.GroupScheme.Torus.MaximalBaseChangeProof`). For fields
   `k K : Type u` with `Algebra k K`, let `G` be smooth affine over `k` and
   let `i` be a closed subgroup whose source is a torus. Then `i` is a
   maximal torus exactly when its base change to `K` is one.

The reduction itself works as follows. Let `K` be the chosen algebraic
closure of `k`. Connected reductivity, splitness of `T`, closedness of the
parabolic and smoothness of `P` survive base change to `K`. Premise 3 gives
maximality of the base-changed torus. The ambient Borel inside the
base-changed parabolic is the witness stored in `IsParabolicSubgroup i`.
Over `K`, `BorelExistence.borelPairInOvergroupData` uses premise 1 in the
identity component of `P`. It picks an ambient Borel inside `P` that contains
the exact torus and gives an actual Borel pair. Premise 2 then gives a
cocharacter and equality of field points. Smoothness and closedness of both
subgroups let `Dynamic.range_eq_parabolic_iff_algClosed_points` turn this
into equality of subgroup functors on every test scheme. Finally,
`exists_range_eq_parabolic_iff_baseChange` descends the presentation to
`k`. It uses the unchanged cocharacter lattice of the split torus `T` and
faithfully flat descent of subgroup functors. The resulting cocharacter
therefore lies in the cocharacter lattice of the original torus over `k`.

## Scope and independence

Nothing is restricted. The proof allows every field and characteristic,
including imperfect fields. It covers general connected reductive groups,
not only semisimple ones, and the full-group parabolic. It also covers
empty root systems and rank-zero tori. The structural inputs above do not
assume `SplitParabolicCocharacterStatement` or
`ParabolicDynamicStatement`. They also do not assume any other unproved
classification proposition. A development check of this module reports
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
The published target and every pair it imports are unchanged.
