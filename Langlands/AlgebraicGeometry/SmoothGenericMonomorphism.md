# Smooth morphisms and dominant tests for monomorphisms

Worker 596.

Let `S` be an arbitrary reduced scheme, let `T → S` be dominant, and let
`f : X → Y` be an actual morphism of schemes over `S`. Assume that `X → S`
is smooth and separated, that the underlying map `f` is smooth, and that
its actual base change to `T` is a monomorphism. There is no finiteness,
affineness, smoothness or separatedness assumption on `Y → S`.

`mono_of_mono_baseChange` proves that the original underlying map `f` is a
monomorphism. It follows that it is an open immersion, because it is flat
and locally of finite presentation. `openImageIso` constructs the actual
isomorphism from `X` to its open image in `Y`; `openImageIso_hom_ι` identifies
its composite with the inclusion as the originally specified map.

## Implemented proof and provenance

This is an internal separatedness and density argument. Form
`P = X ×_Y X`, with its two projections to `X`. The scheme `P` is smooth
over `S`, hence reduced, and its structure morphism is open. Consequently
the inverse image of the dense image of `T → S` is dense in `P`.
The two projections agree after this base change because the base-changed
`f` is a monomorphism. Since their target `X` is separated over `S`, the
published dense-equality theorem for maps out of a reduced scheme shows
that the projections agree globally. The universal property of `P` then
proves that `f` is a monomorphism. The open-immersion conclusion uses
Mathlib's `IsOpenImmersion.of_flat_of_mono`.

The intended application takes `S = Spec R` for a DVR and `T = Spec K`
for its specified fraction field. In that application this lemma can turn
smoothness of the affinization map and its generic-fibre isomorphism into
an open immersion. Neither that smoothness nor a group structure on the
affinization is assumed proved by this module.
