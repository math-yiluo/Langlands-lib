# Geometric fibres after composition of bases

Author: Worker 109.

This internal construction derives transport of quasi-compact morphisms and
geometrically connected fibres from the actual base-composed spaces,
preserved presheaf pullbacks, and ordinary point homeomorphisms. It claims
no external literature theorem as proved. All schemes, fields and tests
retain the arbitrary universe `u`, with sections in `Type (u+1)`.

For any scheme morphism `g : S ⟶ T`, any original transformation `f`, and
any scheme map `a` to its target, `pullbackFromSchemeIso` identifies the
base-composed original presheaf fibre with the actual fibre of `map g f`
over `fromScheme g a`. It applies `map_isPullback` to the original square
and replaces the composed represented test presheaf by the same scheme over
`T`, using `schemeIso`. The resulting square supplies the isomorphism to
the actual presheaf pullback.

`exists_atlas_pullback` obtains an actual etale-surjective scheme atlas
of any scheme fibre of a morphism of algebraic spaces. It uses the
constructed algebraic-space fibre product with the represented test scheme
and then its full presheaf pullback comparison. No supplied representability
of the space morphism is needed.

`quasiCompact_spaceMap` preserves quasi-compactness of a general morphism
of spaces. Each test scheme over `T` and target section determine an
original structure map to `S`; the underlying test scheme, including its
affineness, stays unchanged. The original quasi-compactness condition gives
an etale-surjective atlas of that original fibre from a compact scheme.
Composing the atlas base and using `pullbackFromSchemeIso` gives such an
atlas of the required new fibre. Its underlying source scheme is still the
same compact scheme. The construction works for every affine test and
requires no condition on `g`.

`geometricallyConnectedFibres_spaceMap` treats each field test over `T`
and each target section in the same way, recovering an original structure
map from the spectrum of that very field to `S`. The corresponding target
natural transformation is `fromScheme` of the original section by the
Yoneda comparison. The original hypothesis gives connectedness of that
original fibre's ordinary point space. Its actual atlas gives the
`pointsHomeomorphOfAtlas` from the original point space to that of the
composed original fibre. The presheaf fibre isomorphism then gives a second
ordinary point homeomorphism to the new fibre. Transport across their
composite proves the required connectedness for every field and every
structure map. No algebraic closure, representability, or smoothness
hypothesis is added to this transport result.

These are properties of the actual composed morphism `spaceMap g f`.
Structural quasi-separatedness over the composed base and the arithmetic
uniform estimate still need further work. This module does not establish
the unconditional adelic smooth-openness target.
