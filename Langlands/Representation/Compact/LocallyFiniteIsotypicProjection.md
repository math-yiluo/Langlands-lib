# Isotypic projections on locally finite compact representations

`IsotypicProjection.projection` uses the specified simple module's
isotypic component as range and the sum of the other isotypic components
as kernel. This formula gives the zero projector when the type is absent.
Module maps between different carriers preserve both parts. For group
representations the resulting idempotent has range equal to the sum of
intertwiner images from the chosen type. It preserves every invariant
subspace, including the orbit span of its input.

This internal construction supplies a common compact-type projector for
the finite-dimensional restriction in Langlands, *On the notion of an
automorphic representation* (1979), Proposition 2, printed pp. 205–206
(Corvallis Part I PDF pp. 200–201). The implementation uses the existing
block projections for `K`-finite duality and Mathlib's isotypic
decomposition of semisimple modules. `KFiniteDual.isSemisimpleModule`
provides the required semisimplicity for the weakly continuous locally
finite compact actions.
