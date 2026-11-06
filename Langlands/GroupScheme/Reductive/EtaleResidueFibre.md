# Actual group fibres at a prescribed etale residue extension

Author: Worker 1683.

This module is `Langlands.GroupScheme.Reductive.EtaleResidueFibre`.
It is an internal adapter derived from the exact `residue_over` equation
in `Langlands.AlgebraicGeometry.EtaleResidueExtensionData` and the published
actual group-object base-change composition isomorphism
`Langlands.GroupScheme.baseChangeCompIso`. It needs no new literature
assertion. The residue-extension constructor that supplies its input
implements Stacks Tags 00UD and 02LF; this module only establishes the
actual group and inclusion comparisons used by the reductive-locus proof.

## Actual fields and base maps

Let `d : EtaleResidueExtensionData S s K`. Write `U` for its neighbourhood,
`p : U → S` for its projection, `u` for its point, and `ε : κ(u) ≅ K`
for its actual scheme residue-field isomorphism. The input already proves
that the specified `K`-valued point over `s` is
`Spec.map ε.hom ≫ U.fromSpecResidueField u ≫ p`.

`d.extensionPoint` is the original morphism
`Spec K → Spec κ(s) → S`, using the specified scalar map into `K`.
`d.inverseResiduePoint` is `Spec.map ε.inv : Spec κ(u) → Spec K`.
The theorem `inverseResiduePoint_over` composes the input equation with
this inverse isomorphism and cancels the two inverse spectrum maps. It
proves that the composite from `Spec κ(u)` through `Spec K` to `S`
is exactly `U.fromSpecResidueField u ≫ p`.

## Constructed actual group isomorphism

For any actual group scheme `G/S`, without a smoothness, affineness,
connectedness, or reductivity assumption, `d.groupFibreIso G` identifies

1. the pullback of `G` along the original `K`-valued point, further pulled
   back along `Spec κ(u) → Spec K`; and
2. the actual residue fibre at `u` of the actual pullback `G_U`.

Its source and target are group schemes over the identical scheme
`Spec (U.residueField u)`. The construction first uses the inverse of
the base-change composition comparison to combine the two source
pullbacks. It then transports along the exact base-map equation
`inverseResiduePoint_over`. Finally it uses the base-change composition
comparison for `Spec κ(u) → U → S` to obtain the target. Every object is
an application of the existing `GroupScheme.baseChange` functor.

## Closed split-torus inclusions

Given an actual group scheme `T/Spec K` and an inclusion
`i : T → G_K`, `d.torusFibreInclusion G T i` is the pullback of `i`
along `Spec κ(u) → Spec K`, followed by the homomorphism of
`d.groupFibreIso G`. Its source is the actual pullback of the supplied
`T`, rather than an independently chosen torus.

`torusFibre_isSplit` proves this source is split when `T` is split,
using preservation of the published actual split-torus predicate under
base change. `torusFibreInclusion_isClosed` proves that the resulting
inclusion is a closed subgroup when the supplied `i` is closed: closed
subgroups remain closed under base change, and composition with the
underlying scheme isomorphism of `groupFibreIso` preserves closedness.

The constructions are uniform in the arbitrary universe `u`. They do
not require finiteness or separability of `K` once the data `d` have
been supplied; those hypotheses are used by `etaleResidueExtension` to
construct `d`. They construct no maximal torus, assert no maximality
property of an inclusion, and do not prove relative torus lifting,
centralizer spreading, or openness of the reductive geometric
identity-component locus. The inspected constructor uses only
`propext`, `Classical.choice`, and `Quot.sound`.
