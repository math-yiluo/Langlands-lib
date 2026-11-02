# Quasi-coherence from principal-open scalar base change

Let `f : X → Spec R` be any scheme morphism and `M` an ordinary module
sheaf on `X`. The theorem
`isQuasicoherent_pushforward_of_isIso_principalOpenScalarSectionsBaseChangeMap`
proves that the actual direct image `f_* M` is quasi-coherent when, for every
`r : R`, the specified `scalarSectionsBaseChangeMap` is invertible for the
square obtained by restricting to `D(r)` and identifying that open with
`Spec (Localization.Away r)`. The total-space arrow is the inclusion of
`f⁻¹ D(r)`, its structure map is the restricted `f` followed by
`basicOpenIsoSpecAway r`, and the coefficient sheaf is the actual pullback of
`M`. The theorem has no additional finiteness or quasi-coherence hypothesis.

The intermediate `directImageRestrictionSectionsEquiv` works for any open
`V`, ring map `φ : R → T`, and morphism `i : V → Spec T` satisfying
`i ≫ Spec.map φ = V.ι`. It identifies the restricted-scalars relative sections
of the actual pullback of `M` on `f⁻¹ V` with the actual `R`-module of sections
`(f_* M)(V)`. It composes the base-ring sections isomorphism, inverse composite
pushforward comparison, the inverse restriction-to-pullback comparison on
`X`, the restriction/pushforward comparison, and
`openPushforwardSectionsLinearEquiv`.

`directImageRestrictionSectionsEquiv_sectionsBaseChangeMap` proves that this
equivalence carries the specified ordinary sections base-change map to the
restriction from `(f_* M)(⊤)` to `(f_* M)(V)`. The proof computes the pullback
unit using `pullback_unit_app_comp_restrictFunctorIsoPullback_inv`, unfolds the
restriction/pushforward comparison, and combines the resulting three
presheaf restriction maps.

`isLocalizedModule_directImageRestriction` additionally assumes that `T` is a
localization of `R` at a submonoid and that the specified scalar comparison is
invertible. It transports `isLocalizedModule_sectionsBaseChangeMap` through
the displayed linear equivalence and its compatibility with the actual map.
`principalOpenBaseChangeSquare` supplies the commuting equality for the
principal-open presentation. Applying this localization result for every
`r` makes the direct image localizing as a sheaf of `R`-modules. Mathlib's
`isIso_fromTildeΓ_iff_isLocalizing` and
`isQuasicoherent_iff_isIso_fromTildeΓ` then give the theorem.

This is an internal derived construction from the published actual sections,
restriction and base-change APIs and Mathlib's localization and tilde
criteria. It does not establish the scalar comparison hypotheses, prescribed
cubic rank, local freeness, or arbitrary sheaf base change of the host task.
