# Proper projection from the scalar-extended analytic space

For an isometric embedding `K → L` of complete ultrametric normed fields,
`pointProjection` is the continuous natural projection from the underlying
space of the actual scalar extension to the original analytic space. It
expresses `localizedProjection` on the original point types using the
canonical homeomorphisms for `ULift`. It is surjective because each extended
chart projects onto the original chart.

`projection_isProperMap` proves that the projection of a scalar-extended atlas
is closed and has compact fibres. For a closed subset upstairs, its image
can be tested against the original chart quasinet. The preimage of the
image in an original chart spectrum is the image of a closed subset of its
extended chart spectrum. This image is compact and lies in a Hausdorff
spectrum, so it is closed. A fibre over an original point lies inside the
extended chart corresponding to any chart containing that point. It is the
image of a closed fibre in that compact spectrum. These arguments apply to
locally Hausdorff atlases with arbitrary index universes.

`pointProjection_isProperMap` gives the same property for the natural
projection in the analytic localization. In particular, the inverse image
of every compact set is compact.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
§1.4, printed p. 30 (PDF p. 27), describes the compact projection of the
scalar extension. The proof uses the original quasinet closure test in
§1.1, Lemma 1.1.1(i), printed pp. 13–14 (PDF pp. 10–11), and the inverse-image
formula for the extended chart ranges. The registered source
`berkovich-1993-etale-cohomology` has SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
