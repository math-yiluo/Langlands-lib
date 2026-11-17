# Affine open covers carrying root-datum character maps

This internal derived module assembles the neighbourhood-dependent actual
character formulas from `LocalRootDatumCharacterBaseChange` on one affine open
cover. It also preserves the torus squares of two ambient homomorphisms on that
cover. The coefficient ring is arbitrary; no local-ring assumption is used.

`HasAffineOpenRootDatumTorusCharacterMap tau P Q` is a Prop-valued predicate.
It supplies an actual affine open cover of Spec R. Each chart carries the
existing `HasRootDatumTorusCharacterMap` predicate for the canonical coordinate
pullback of tau and the same supplied coordinate root data P and Q. Its natural
number and root-datum isogeny may vary from chart to chart.

`HasZariskiLocalRootDatumTorusCharacterMap.affineOpenCover` proves this
predicate from the preceding neighbourhood predicate. It chooses one open
neighbourhood and one root-datum isogeny for every base point, forms the open
cover given by these neighbourhoods, and takes Mathlib's affine refinement of
that cover. The map from each affine chart factors through its chosen open, so
its inverse image of that open is the whole chart. The supplied character
formula therefore applies to the actual chart map.

`splitTorus.coordinateBaseChangeHom_square_scheme` works for any map b from
one scheme to another. It proves that a torus square for an ambient group-scheme
homomorphism pulls back to a torus square in the canonical split-torus
coordinates. The proof maps the original square through base change and
cancels the forward and inverse target coordinate isomorphisms.

`HasAffineOpenRootDatumTorusCharacterMap.common_torusSquares` assumes two
ambient homomorphisms whose restrictions factor through the same coordinate
torus homomorphism tau. It keeps the actual affine cover and packages the
chart's character formula and the two pulled-back squares into
`HasCommonRootDatumTorusMap` on each chart. The theorem
`HasZariskiLocalRootDatumTorusCharacterMap.common_torusSquares` composes the
neighbourhood-to-affine-cover construction with this packaging.

The source and target root data are supplied throughout. The assertions about
character maps do not assert that these data are fibrewise root data of the
ambient groups; such geometry remains a separate premise for consumers.
This module constructs no normalized root parametrizations or torus
conjugators. In particular it does not prove the intrinsic
`AffineSplitSurjectionRootDatumStatement` or the unconditional rigidity target.

The provenance is direct composition of the preceding neighbourhood predicate,
Mathlib's open-cover and affine-refinement constructions, functoriality of group
scheme base change, and the definitions of the existing character-map and
common-torus-map packages. These are internal assembly lemmas, with no additional
source theorem asserted.
