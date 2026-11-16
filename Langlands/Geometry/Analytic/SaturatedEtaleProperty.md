# A canonical étale property on saturated strong maps

Author: Worker 208.

The definition `SaturatedAtlasPresentation.strongEtale` is an internal
morphism property on `SaturatedAtlasPresentation.{u, v, w} K`, for a
complete ultrametric normed field `K : Type u`. The space and original
atlas-index universes `v` and `w` are independent.

For an actual saturated strong map `f : A ⟶ B`, use the existing compatible
functor and actual saturation functor to extend `f` to the constructed
saturations of `A.presentation` and `B.presentation`. `strongEtale f` means
that this extension satisfies the existing `IsEtaleAllPieces` predicate.
The compatible functor derives coherence from the source's stored
all-local-domains property; no additional map or geometry is supplied.

`strongEtale_of_isQuasiIso` applies the earlier finite-étale saturation
extension theorem, so every full strong quasi-isomorphism has this
property. `strongEtale_comp` uses functoriality of the actual extension and
the existing all-pieces composition theorem. Identities are full
quasi-isomorphisms; together these facts supply an `IsMultiplicative`
instance for the property.

`strongEtale_precomp_quasiIso_iff` and
`strongEtale_postcomp_quasiIso_iff` show that a quasi-isomorphism on either
side preserves and reflects this property. The actual saturation functor
preserves the full quasi-isomorphism condition. Its composition equation
then reduces the two assertions to the source and target invariance
proved in `QuasiIsoSourceEtale` and `QuasiIsoTargetEtale`.

This definition organizes the proved strong-map infrastructure for a
subsequent localization argument. This module does not identify it with
the existing localized `etale` predicate, assert general étale right
cancellation, or prove the unrestricted pointwise-lifting target. All
results are internal consequences of existing constructions and the
included derived helpers, without an external theorem claim, Hausdorffness
or an unproved geometric input.
