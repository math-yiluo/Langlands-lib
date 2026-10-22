# Coherence targets for the canonical pullback unit

The three proposition definitions in namespace `Langlands.Scheme.Modules` concern
`pullbackUnitIso f : f^* O_Y ≅ O_X`, defined in `PullbackUnit` for every morphism
of schemes `f : X ⟶ Y`. Each scheme lies in an arbitrary fixed universe `u`, and
`O_X` is exactly `SheafOfModules.unit X.ringCatSheaf`.

- `PullbackUnitAdjunctionStatement` says the forward map corresponds to
  `unitToPushforwardUnit f` under Mathlib's actual scheme-module
  pullback-pushforward adjunction.
- `PullbackUnitIdentityStatement` says that for the identity of `X`, the forward
  unit map is the component of `Scheme.Modules.pullbackId X` at `O_X`.
- `PullbackUnitCompositionStatement` says that for `f : X ⟶ Y` and `g : Y ⟶ Z`,
  the map from `f^*(g^* O_Z)` to `O_X` obtained first from
  `Scheme.Modules.pullbackComp f g` and then the unit map for `f ≫ g` equals
  the map obtained by applying `f^*` to the unit map for `g` and then applying
  the unit map for `f`.

`PullbackUnitCoherenceStatement` is the conjunction of these three targets.
These are statements only; this module proves none of them and does not assume
them as instances. No tensor construction or full monoidal coherence is claimed.

These targets are internal compatibility requirements for the canonical
construction. They use the existing comparison orientations in pinned Mathlib
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` (commit
`5ed2965256430c3649e86755f9576b54eca72435`) and the adjoint unit map in
`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`.
They are not presented as a transcription of a numbered literature theorem.
The intended separate proof reduces the equations to the structure-sheaf
maps through the adjunction; that proof remains an explicit obligation.
