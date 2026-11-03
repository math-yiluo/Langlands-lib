# The actual schematic image of an affine orbit

This internal construction uses the published scheme action, scheme-theoretic
image and flat-base-change APIs. For an actual action of a flat group scheme
on an affine scheme, and a quasi-compact orbit map of a rational section, it
constructs the schematic image over the same base, its closed inclusion and
the canonical quasi-compact schematically dominant projection. A reduced
acting group gives a reduced image.

The image is stable under the original action. Pulling its projection back
along the flat acting group preserves schematic dominance. The group action
law shows that the action composed with this dominant map factors through
the image. Kernel containment then supplies the action morphism on the
image. Cancellation of the closed inclusion proves the action laws and its
all-test compatibility with the original action.

The identity of the group supplies the distinguished point of the image.
Its orbit map for the restricted action is exactly the image projection.
No orbit closedness, flatness of the projection, or quotient existence is
asserted here. Worker 362 authored this derivation from existing Library
constructions; no external theorem is assumed.
