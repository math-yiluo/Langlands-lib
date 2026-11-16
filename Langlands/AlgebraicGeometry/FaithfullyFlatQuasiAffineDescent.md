# Canonical affine-hull presentation after quasi-affine descent

Worker 585.

The internal helper
`Langlands.AlgebraicGeometry.FaithfullyFlatQuasiAffineDescent.isQuasiAffine_of_isPullback`
works in every universe. Let `P → X`, `P → B`, `X → Y`, `B → Y` be a
cartesian square of schemes. If `Y` and `B` are affine, `B → Y` is flat
and surjective, and `P` is quasi-affine, then `X` is quasi-affine. There
are no finite-presentation or noetherian assumptions.

Under these same hypotheses, the construction `affineHullOpen` is the
open image of the canonical map `X → Spec Γ(X, ⊤)`, and
`affineHullOpenIso` identifies `X` with that open subscheme. The identity
`affineHullOpenIso_hom_ι` says that the isomorphism followed by the open
inclusion is exactly the canonical map. These constructions provide
actual open-subscheme data, using the descent lemma below.

This is a derived internal result, adapting the implemented proof of
[`FaithfullyFlatAffineDescent.isAffine_of_isPullback`](FaithfullyFlatAffineDescent.md).
It uses the existing Library and Mathlib results described below; it does
not assert a new translation from the literature.

The projection `P → X` is surjective and quasi-compact by base change.
Consequently `X` is quasi-compact, and the published
`FieldExtensionAffineDescent.quasiSeparatedSpace_of_surjective` gives its
quasi-separatedness. Flat base change of global sections
(`LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback`) then makes the
global-section square a pushout. Taking spectra gives a cartesian square
of affine schemes. The induced map `Spec Γ(P) → Spec Γ(X)` is flat and
surjective, since it is the base change of the map isomorphic to `B → Y`.

Naturality of the canonical maps to spectra of global sections, together
with pullback pasting and cancellation, shows that `P → Spec Γ(P)` is
the pullback of `X → Spec Γ(X)` along that flat surjective affine map.
Quasi-affineness of `P` makes the former an open immersion. Mathlib's
fpqc descent of open immersions gives the same property for the latter.
Combining this with the already proved quasi-compactness gives precisely
Mathlib's `Scheme.IsQuasiAffine X`.

This lemma supplies a descent step for maximal-torus moduli. It does
not construct those moduli or establish their local quasi-affineness.
