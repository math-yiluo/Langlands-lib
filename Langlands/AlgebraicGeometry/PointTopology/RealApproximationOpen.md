# Real approximation on open affine subschemes

`HasRealApproximation.of_isOpenImmersion` transfers approximation from an
affine rational scheme to any affine open subscheme. An open immersion induces
an open embedding on actual real points. The image of a real open neighborhood
therefore contains the scalar extension of a rational point of the ambient
scheme. The map from the spectrum of the reals to the spectrum of the rationals
is surjective on underlying points, so the original rational point also lands
in the open subscheme. Lifting that point through the open immersion and using
injectivity on real points proves density.

This internal lemma uses the published open-embedding theorem for scheme
points, the affine evaluation comparison, and the open-immersion lifting
property.
