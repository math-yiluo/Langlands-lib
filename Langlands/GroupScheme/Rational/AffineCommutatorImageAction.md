# The actual pointed action on the affine commutator image

This internal adapter supplies the actual action on the closed commutator
image used in the route of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), Lemma 3.3.4, printed pp.108–109 (PDF pp.134–135),
registered source `conrad-gabber-prasad-2015-pseudo-reductive`.
It combines `AffineCommutatorImageStability` with the actual nongroup
pointed-scheme construction `PointedCoordinateAction`.

Let `G`, `H`, and `K` be affine group schemes over an arbitrary field in
universe `u`, with compatible actual actions of a commutative group scheme
`S`. Flatness over the field is supplied by Mathlib. The two input homomorphisms
`i : H → G` and `j : K → G` intertwine the actions on every test scheme.
The closed image inclusion is a monomorphism because it is a closed
immersion. Its image origin maps to the identity, and its all-test
stability was proved by schematic descent in the imported module.

`imageAction` applies `PointedAction.ofStableInclusion` to these proved
facts. It is an actual scheme action on `imageScheme i j`, with
`imageOrigin i j` as its fixed rational point. The scheme image need not
be a group. `imageAction_act_comp` and
`imageInclusion_isPointedEquivariant` prove agreement with the ambient
action and preservation of the distinguished point.

`imageFactor_equivariant` proves that translating both inputs and then
mapping to the image equals translating their image point. Cancellation
against the monomorphic inclusion reduces this identity to the previously
proved equivariance of the actual commutator map.

All test schemes remain arbitrary. No coordinate decomposition, weight
support bound, geometric integrality, or generated-subgroup conclusion is
claimed here. These arguments are an internal implementation of the
image-action step motivated by CGP; no stronger theorem is attributed to
the cited passage.
