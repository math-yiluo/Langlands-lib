# Canonical open presentations after etale descent of quasi-affineness

Worker 585. This is an internal derived construction for Task 6831.

For any morphism f : X → S and any etale cover U_i → S, assume that each
projection X ×_S U_i → U_i has the following property: its inverse image
of every affine open in U_i is quasi-affine. The theorem
`Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent.quasiAffineOver_of_etaleCover`
proves that the inverse image of every affine open in S is quasi-affine.
All schemes have universe u; the cover index may lie in an independent
universe v and may be infinite. No noetherian, smoothness or finiteness
hypothesis on S or X is imposed. Quasi-affine always means Mathlib's
`Scheme.IsQuasiAffine`, including quasi-compactness.

For each affine open V in S, `affineOpenHull` constructs the open image
of the canonical map from f⁻¹(V) to the spectrum of its global sections.
`affineOpenHullIso` identifies f⁻¹(V) with that open subscheme. The
identity `affineOpenHullIso_hom_ι` says that this isomorphism followed
by the open inclusion is the canonical map to the spectrum. These are
actual open-subscheme and isomorphism data built using the descent theorem.

The proof first treats an affine base with an equivalent affine-test
hypothesis: for every affine open immersion B → U_i, the pullback
X ×_S B is quasi-affine. To accommodate arbitrary index universes it
passes to Mathlib's cover indexed by points of S, choosing one original
cover component above each point. Etale maps are open, so the resulting
cover is quasi-compact in the cover sense. Mathlib's finite affine
refinement gives a finite affine etale cover with open-immersion maps
into the chosen original components. The affine tests give quasi-affineness
of the pullbacks to these finitely many pieces. The finite affine
flat-family result in [QuasiAffineCoverDescent](QuasiAffineCoverDescent.md)
then descends quasi-affineness to X.

The helper `isQuasiAffine_pullback_affine_open` obtains those affine
tests from the stated inverse-image-open hypothesis. An affine open
immersion B → U_i identifies B with an affine open in U_i. Pullback
pasting identifies X ×_S B with the inverse image of that open in
X ×_S U_i, and quasi-affineness transports through the isomorphisms.
`isQuasiAffine_of_etaleCover` applies this to an affine base.

For an arbitrary base, fix an affine open V in S and restrict f to V.
Pull the given etale cover back to V. Each affine open-immersion test
B into a pulled cover member also gives an affine open immersion into
the corresponding original cover member, because V → S is an open
immersion. The previous helper gives quasi-affineness of X ×_S B.
Pullback pasting identifies this with the required test for f restricted
to V, and the affine-base result finishes the proof. The open presentations
then follow by Mathlib's canonical open immersion into the affine hull.

The provenance is entirely internal: the module combines the cited
Library descent construction with Mathlib's etale openness, finite affine
cover refinement, scheme restrictions and pullback identities. It does
not assert a translation of an additional structural theorem from the
literature. This supplies the generic etale descent step; local
quasi-affineness of maximal-torus moduli remains a separate obligation.
