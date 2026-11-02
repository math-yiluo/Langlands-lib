# Effective descent and compact representation of etale chart images

This derived construction completes the effective descent step in the registered
Stacks Lemma 67.50.1 (Tag 03XW), specialized to a monomorphic map of fppf
sheaves to a scheme. All schemes remain over the original base in the
arbitrary universe `u`.

`compactImageDescent` proves the exact interface used by
`EtaleLocalImageInduction`. Write `A` for the local image of the given
affine open chart in the original sheaf. Etaleness shows that `A` is an
open subsheaf, so it is an actual fppf sheaf. The explicit compact
representation of its saturation is fed to
`saturatedLocalImageGeometry`, giving a compact scheme `W`, its
monomorphic, locally finite type and locally quasi-finite map to the
affine base chart, and a cartesian, locally surjective map `h_W → A`.
Zariski's main theorem in `QuasiAffineChart` makes `W` quasi-affine.

`LocallyQuasiFiniteDescent.exists_iso_of_quasiAffine` then constructs a
scheme `Y` representing `A` and a map `r : W → Y` compatible with that
representation. The cartesian square makes `h_W → A` etale; transporting
along the representing isomorphism makes `r` etale and fppf locally
surjective. The published scheme-image result gives surjectivity of
`r` on underlying points. Thus `Y` is compact as the continuous image
of `W`, which proves the full compact representation interface.

`of_affine_etale` applies the already checked finite-field-fibre
induction with this proved interface. Its conclusion represents the
local image itself by a compact scheme. It assumes no global
surjectivity of the etale base morphism. It does not yet perform the
affine atlas neighborhood reduction or prove the final schemehood
statement.

`affineEtaleImageModel` selects an actual representing scheme and an
actual natural isomorphism from `of_affine_etale`. Its output is a
dependent pair: a scheme over `S` equipped with a proof that its underlying
space is compact, followed by an isomorphism from its functor of points
to the local image. Classical choice selects the scheme and the
isomorphism from the proved compact-representation existential. This is
an internal witness-selection construction for the effective-descent
argument; it adds no hypothesis to that argument. Consumers can use its
scheme, compactness proof and isomorphism directly.

The implementation uses the independent effective descent proof in
`LocallyQuasiFiniteDescent.Core`, whose argument descends global
functions and compares locally surjective presentations with the same
kernel. The paired documentation of that module describes that
implemented route.
