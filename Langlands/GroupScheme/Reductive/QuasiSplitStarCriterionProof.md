# The absolute star criterion for quasi-split groups: proof

This module proves the published proposition
`Langlands.GroupScheme.QuasiSplitStarCriterionStatement`
([`QuasiSplitStarCriterionStatement`](QuasiSplitStarCriterionStatement.md)) as the theorem
`Langlands.GroupScheme.quasiSplitStarCriterion`, of type exactly
`QuasiSplitStarCriterionStatement.{u}` with no additional hypothesis.

## Statement proved

Let `k` be any field, `k_s = SeparableClosure k`, and `G` a group scheme over `Spec k`
whose structure morphism is affine and locally of finite type, with `IsQuasiSplit G`.
For every `d : GaloisPinningData k k_s G`, `G` has a split maximal torus over `k`
(`HasSplitMaximalTorus G`) if and only if `d.starAction σ = 1` for every
`σ ∈ Aut_k(k_s)`. The star action is the action on the full based root datum
of `(G_{k_s}, T_{k_s})`, on the actual character and cocharacter lattices of the base change
of the `k`-torus `T` of `d`.

## Two helper lemmas

`trivial_star_transport` (private). If `d.starAction σ = 1` for all `σ`, then the same holds
for any other `d' : GaloisPinningData k k_s G`. The published
`StarActionIndependence.starActionIndependence` gives an equivalence `e` of root data from
`d` to `d'` with `e ∘ d.starAction σ = d'.starAction σ ∘ e`. With `d.starAction σ = 1` this
says that the weight map of `d'.starAction σ` fixes every character in the image of
`e.weightEquiv`, which is surjective. `StarActionIndependence.equiv_ext_of_weightMap`
(an automorphism of the root datum is determined by its weight map) then gives
`d'.starAction σ = 1`.

`split_of_fixes_characters` (private). Let `T` be a `k`-torus with `T_{k_s}` split and every
geometric character fixed by `characterLattice.galoisRepresentation k k_s T σ` for every `σ`.
Then `T` is split over `k`. `IsTorus.of_baseChange` shows that `T` is a torus, hence of
multiplicative type. Splitness of `T_{k_s}` gives an isomorphism of `T_{k_s}` with the
coordinate split torus `G_m^I` over `k_s` for a finite type `I`. Let `S = G_m^I` be the
coordinate split torus over `k` (`splitTorus.commGroupScheme`); `splitTorus.baseChangeIso`
identifies `S_{k_s}` with `G_m^I` over `k_s`, and `CommGroupScheme.isoOfGroupIso` turns the
composite into an isomorphism `T_{k_s} ≅ S_{k_s}` of commutative group schemes.
`characterLattice.congr` turns it into an equivalence of the geometric character
lattices. The Galois action on both lattices is trivial, the one of
`T` by hypothesis and the one of `S` by
`TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus`, so the equivalence is
equivariant. `characterLattice.isoOfEquivariantAbsoluteEquiv`, the absolute-Galois
character equivalence for groups of multiplicative type, gives an isomorphism `S ≅ T` over
`k`, and `IsSplitTorus.of_iso` concludes.

## Split implies trivial star action

Let `i : T → G` be a split maximal torus over `k`. The published `splitPinningExistence`
(for the connected reductive group `G`, the first field of `IsQuasiSplit G`) gives a
split pinning `p` of `G` over `k`; its torus `p.torus` is split. The scalar extension
`p.baseChange` to `k_s` (`Reductive/PinningBaseChange`) is a pinning of `G_{k_s}` whose
torus is the base change of `p.torus`, and `GaloisPinningData.ofTorusIso`
(`Reductive/TorusTransportPinning`) with identity isomorphisms makes it Galois pinning
data `dSplit` with `k`-torus `p.torus` and inclusion `p.inclusion`.

For every `σ`, the ordinary action `dSplit.galoisAction σ` is the identity: by
`StarActionIndependence.galoisAction_weightMap_apply` its weight map is the Galois
representation on the characters of `p.torus`, which is trivial by
`TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus` (every geometric character
of a split torus is the base change of a character over `k`), and
`StarActionIndependence.equiv_ext_of_weightMap` gives equality on the full root datum.
The identity lies in the Weyl group, so `GaloisPinningData.starAction_eq_one_iff` gives
`dSplit.starAction σ = 1`. `trivial_star_transport` transfers this to the given `d`.

## Trivial star action implies split

The published `starActionQuasiSplit` gives Galois pinning data `dBorel` whose star action
equals its ordinary Galois action. By `trivial_star_transport`, `dBorel.starAction σ = 1`
for every `σ`, so `dBorel.galoisAction σ = 1`, and by
`StarActionIndependence.galoisAction_weightMap_apply` the Galois action on the geometric
characters of the `k`-torus `dBorel.torus` is trivial. Its base change to `k_s` is split by
the field `dBorel.isSplitTorus`, so `split_of_fixes_characters` shows that `dBorel.torus`
is split over `k`.

It remains to show that `dBorel.inclusion` is a maximal torus over `k`. By
`fieldExtension_fpqc`, `Spec k_s → Spec k` is surjective, flat and quasi-compact, and so is
its pullback along the structure morphism of `G`. The base change of `dBorel.inclusion` to
`k_s` is a closed immersion (part of the maximal-torus field `dBorel.isMaximalTorus`), and
the squares of `baseChange_map_isPullback` together with the descent of closed immersions
along fpqc morphisms (`closedImmersion_descendsAlong_fpqc`,
`Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent`) show that `dBorel.inclusion` is a
closed subgroup. `IsMaximalTorus.of_baseChange` then gives that `dBorel.inclusion` is a
maximal torus of `G`, so `G` has the split maximal torus `dBorel.torus`.

## Published inputs

Names in namespace `Langlands.GroupScheme`, by module under `Langlands.GroupScheme`
unless stated otherwise:

- `Reductive.StarAction`: `GaloisPinningData`, `GaloisPinningData.galoisAction`,
  `GaloisPinningData.starAction`, `GaloisPinningData.starAction_eq_one_iff`.
- `Reductive.StarActionIndependenceProof`: `StarActionIndependence.starActionIndependence`,
  `StarActionIndependence.equiv_ext_of_weightMap`,
  `StarActionIndependence.galoisAction_weightMap_apply`.
- `Reductive.StarActionQuasiSplitProof`: `starActionQuasiSplit`.
- `Reductive.SplitPinningExistenceProof`: `splitPinningExistence`.
- `Reductive.PinningBaseChange`: `SplitPinning.baseChange`.
- `Reductive.TorusTransportPinning`: `GaloisPinningData.ofTorusIso`.
- `SimplyConnected.TrivialStarInnerTwist`:
  `TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus`.
- `Torus.AbsoluteCharacterIsomorphism`: `characterLattice.isoOfEquivariantAbsoluteEquiv`.
- `Torus.SplitLatticeBaseChange`: `CommGroupScheme.isoOfGroupIso`.
- `Torus.LatticeGalois`: `characterLattice.congr`.
- `Torus.Lattice`: `splitTorus.commGroupScheme`.
- `Torus.Split`: `isSplitTorus_splitTorus`, `IsSplitTorus.of_iso`, `splitTorus.baseChangeIso`.
- `Torus.BaseChange`: `IsTorus.of_baseChange`.
- `Torus.MaximalBaseChangeReflection`: `IsMaximalTorus.of_baseChange`.
- `BaseChangeReflection`: `fieldExtension_fpqc`.
- `CentralIsogeny.FpqcReflection`: `baseChange_map_isPullback`.
- `Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent`:
  the instance `closedImmersion_descendsAlong_fpqc`.

Mathlib supplies `MorphismProperty.of_isPullback`,
`MorphismProperty.of_isPullback_of_descendsAlong` and `IsPullback.of_hasPullback`.

## Source

The mathematics is that of J. S. Milne, *Algebraic Groups* (2017), as recorded in the
statement's Markdown: for a quasi-split group the star action is the ordinary action on a
torus in a Borel subgroup over `k` (Proposition 25.28(a)), and a torus with trivial
Galois action on its character lattice is split (Theorem 12.23).

No hypothesis beyond those of the statement is used; there is no restriction on the
characteristic of `k`. `#print axioms` reports only `propext`, `Classical.choice` and
`Quot.sound`.
