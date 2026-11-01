# Line bundles with two compatible axis rigidifications

Fix four schemes and maps `e : S → X`, `t : S → Y`, `i : X → Z`,
`j : Y → Z`, with an equality `h : e ≫ i = t ≫ j`. This module defines
the category of actual module sheaves on `Z` with compatible
trivializations along `i` and `j`, and its full subcategory of line bundles.

## Actual objects, morphisms and isomorphisms

`TwoAxisRigidifiedModule e t i j h` stores an actual `Z.Modules` object
as `carrier` and a `TwoAxisRigidification e t i j h carrier`. Thus it
retains both chosen axis isomorphisms and their equality after
restriction to the common base. The definition and comparison convention
of the compatibility condition are in `TwoAxisRigidification.md`.

For objects `M` and `N`, `Hom M N` consists of actual module morphisms
`f : M.carrier → N.carrier` satisfying both equations

```text
M.rigidification.first.hom  ≫ i* f = N.rigidification.first.hom
M.rigidification.second.hom ≫ j* f = N.rigidification.second.hom.
```

Identities and compositions are those of the underlying modules. Functoriality
of module pullback proves preservation of both equations. `forget` is
faithful and keeps exactly the underlying module. `isoMk` lifts a module
isomorphism satisfying both displayed equations; the inverse equations
follow by cancellation of the forward isomorphism.

`TwoAxisRigidifiedLineBundle e t i j h` is the full subcategory cut out
by `IsLocallyFreeRankOne M.carrier`. In its namespace, `ofLineBundle`
equips a supplied actual line bundle with supplied compatible
rigidification data. `forgetToRigidified` retains the rigidifications
and forgets the rank-one property. The faithful `forget` instead retains
the actual line bundle and forgets both rigidifications. Its `isoMk`
lifts the compatible module isomorphism to the full subcategory.

## Pullback and comparisons

A second diagram has maps `e'`, `t'`, `i'`, `j'`. A map to the first
consists of `fz : Z' → Z`, `fx : X' → X`, `fy : Y' → Y`, `fs : S' → S`,
with

```text
i' ≫ fz = fx ≫ i             j' ≫ fz = fy ≫ j
e' ≫ fx = fs ≫ e             t' ≫ fy = fs ≫ t.
```

`TwoAxisRigidifiedModule.pullback` uses actual module pullback along
`fz` and the canonical `TwoAxisRigidification.pullback`. Its action on
morphisms is module pullback. Preservation of the two trivializations is
the preservation result for `RigidifiedModule.pullback`, applied separately
to each axis.

`pullbackId` lifts the ordinary module `Scheme.Modules.pullbackId`
comparison. Its two compatibility proofs are the unconditional published
`RigidifiedModule.pullbackIdentity` theorem, once for each axis.
`pullbackComp` similarly lifts `Scheme.Modules.pullbackComp` and uses
`RigidifiedModule.pullbackComposition` twice. Naturality follows from the
naturality of the underlying module comparisons and faithfulness of
forgetting rigidifications.

`pullbackCongr` identifies pullback functors for four equal scheme maps.
Eliminating those equalities leaves identical functors: equality witnesses
for the diagram equations have no further effect by proof irrelevance.

The corresponding line-bundle `pullback` uses `ObjectProperty.lift`
and preservation of local rank one under actual module pullback.
`pullbackForgetIso` is the identity comparison with ordinary
`LineBundle.pullback fz`. The line-bundle `pullbackId` and `pullbackComp`
lift the module natural isomorphisms through the full subcategory.
Its `pullbackCongr` again eliminates equalities of the four maps.
None of these constructions takes a coherence proposition as an
unproved premise.

## Provenance and scope

This is internal categorical infrastructure derived from the paired
`TwoAxisRigidificationPullback` construction, the published one-axis
`RigidifiedLineBundle` definitions and `RigidifiedPullbackProofs`, and
Mathlib's full subcategories and module pullbacks. It makes no new
literature assertion.

All schemes have arbitrary universe `u`. No geometric, valuation,
fraction-field or Noetherian hypothesis is imposed. Isomorphism classes
are constructed in `TwoAxisRigidifiedClassPresheaf`; this module asserts
no ordinary Picard comparison, correspondence identification,
representability, gluing or extension theorem.
