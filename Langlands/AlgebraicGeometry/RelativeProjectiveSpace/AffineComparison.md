# Affine-base comparison for relative projective space

This module compares the two actual projective-space constructions over an
affine base. It constructs an isomorphism from the polynomial Proj
`ProjectiveSpace R n` to `RelativeProjectiveSpace (Spec R) n`, compatible
with their structure morphisms and their maps to the integral model.

The construction is derived from the published theorem
`AlgebraicGeometry.ProjSpace.isPullback_map` and
`AlgebraicGeometry.ProjSpace.map_preimage_basicOpen_X`, imported by Lean name
from the Anthropic FLT port, and the published definition of relative projective
space. The two polynomial gradings are the same homogeneous-submodule
grading, and their degree-zero constants maps agree. The algebra on `R`
over the lifted integers is the ordinary integer cast composed with the
inverse lift map.

The polynomial base-change square over the spectrum of the lifted
integers is transported to the chosen terminal scheme by its unique
terminal isomorphism. The pullback universal property then gives the
comparison. Its projection identities imply the corresponding inverse
identities. This is an internal categorical consequence of the published
polynomial base-change theorem; it adds no geometric assumption.

`polynomialToIntegral_preimage_coordinateOpen` specializes the published
coordinate inverse-image theorem to the lifted integer algebra. The
integral-projection identity and composition of inverse images then prove
`affineComparisonIso_hom_preimage_chart`: the comparison identifies every
inverse-image integral coordinate chart with the corresponding standard
polynomial-Proj chart.

The base ring is arbitrary, in the same universe as the schemes, with
dimension zero and the zero ring included. The module constructs no
nontrivial projective bundle, cubic embedding, Hilbert locus or moduli
space.
