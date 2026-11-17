# Products of field-scheme affinizations

All schemes and fields have an arbitrary fixed universe `u`. This is an internal construction supporting the actual group structure on the affinization of a quasi-compact field group.

`FieldAffinization.isPushout_appTop` takes an actual Cartesian square of schemes over `Spec k`, with both factors quasi-compact and quasi-separated, and proves that its actual global-section maps form a pushout of commutative rings. It specializes Mathlib's `isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat` to the top opens. Scheme flatness follows from the field base; the canonical isomorphism `Γ(Spec k,O) ≅ k` supplies the field structure needed for ring-map flatness. Unfolding `appLE` identifies the four maps with actual `appTop`.

`SchemeCategory k` is the full category of schemes quasi-compact and separated over the field. The property `qcSeparated` is stable under composition, base change and post-composition cancellation, so the full category inherits actual finite Cartesian products. The functor `FieldAffinization.functor k` is the composite of the inclusion, relative global sections and relative spectrum. Its underlying scheme is exactly `Spec Γ(X,O)`, its structure map is `Spec` of the actual scalar map, and its map on morphisms is `Spec` of `appTop`.

The natural transformation `unit k` has underlying morphisms exactly `X.toSpecΓ`. Its compatibility with the base follows from naturality of the canonical affinization and the `ΓSpecIso` identities. Its naturality is the same actual scheme naturality identity.

`isPullback_map_fst_snd` applies spectrum to the ring pushout, and transports the base by `ΓSpecIso`. This proves that the actual product comparison is an isomorphism. The terminal comparison is `Spec.map ΓSpecIso.inv`, hence is invertible as well. Together they give `preservesFiniteProducts` and the canonical Cartesian monoidal structure on the affinization functor. The provenance is Mathlib's flat global-sections theorem, spectrum/pushout comparison and categorical group-object infrastructure; no additional mathematical premise is introduced.

This module does not assert finite generation of the global-functions algebra, smoothness or surjectivity of the canonical map, or anti-affineness of a kernel.
