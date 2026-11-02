# Actual sections of an open pushforward

For an ordinary module sheaf `P` on `Spec R` and any open `V`,
`openPushforwardSectionsLinearEquiv` identifies the actual `R`-module of
relative global sections of `V.ι_* (P|V)` with the `R`-module of sections
`P(V)` obtained by restricting the structure sheaf action on the spectrum.
The equivalence is the presheaf transport from the image of the inverse image
of the top open to `V`. Its scalar compatibility follows from
`Hom.app_appIso_inv` and composition of restriction maps of functions.

`openPushforwardSectionsLinearEquiv_unit` shows that this equivalence sends
the restriction-adjunction unit on top sections to the actual restriction
map from `P(⊤)` to `P(V)`. The proof composes the two presheaf restriction maps.
No quasi-coherence or finiteness assumption is used.

These are internal consequences of the relative sections construction in
`DerivedSections` and Mathlib's module restriction and adjunction APIs.
They support localization arguments for direct images, and assert no cubic
rank or arbitrary sheaf base-change theorem.
