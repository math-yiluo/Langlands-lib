# The canonical affinization over an affine principal open

For a quasi-compact, quasi-separated scheme `X` and a global function `f` whose
principal open `X_f` is affine, `affinizationBasicOpenIso` constructs an
isomorphism from the inverse image of `D(f)` under the canonical map
`X → Spec Γ(X, ⊤)` to `D(f)`. Its forward map is the restriction of that
canonical map. The inverse image is `X_f`.

This is an internal construction for the principal-open step of the smooth DVR
affineness argument. It does not assert the existence of a suitable function.
It packages Mathlib's localization and canonical-map APIs.

The auxiliary theorem `isIso_toSpecΓ_restrict_basicOpen` proves the isomorphism.
Quasi-compactness and quasi-separatedness identify `Γ(X_f)` with the localization
of `Γ(X)` at `f`. Its spectrum maps by an open immersion onto `D(f)`.
The canonical-map square identifies its composite with the map from `X_f`.
Affineness of `X_f` makes its canonical map an isomorphism. The restricted map
is therefore an open immersion, and the same square and the localization
range formula make it surjective. A surjective open immersion is an isomorphism.
