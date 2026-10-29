# The constants and structural morphism of polynomial projective space

This is an internal adapter for the published polynomial-Proj construction
in `Langlands.AlgebraicGeometry.ProjectiveSpace`. It preserves that module
and the definition of its structural morphism.

`projectiveSpaceConstantsEquiv R n` identifies the base commutative ring
`R` with the degree-zero part of
`MvPolynomial (Fin (n + 1)) R`. Its underlying map is exactly the published
`projectiveSpaceConstants R n`. Injectivity follows from injectivity of
the constant-polynomial map. A polynomial homogeneous of degree zero has
total degree zero, and hence equals the constant polynomial with its
constant coefficient; this proves surjectivity. The construction includes
the zero ring and `n = 0`.

`projectiveSpaceCoordinateRing_finiteType` supplies finite generation of the
coordinate ring over the degree-zero ring. A polynomial ring in finitely
many variables is a finite-type algebra over `R`. The composite of the
constants map with the degree-zero inclusion is its usual algebra map.
Mathlib's ring-homomorphism finite-type cancellation theorem therefore
gives finite type for the inclusion, hence the asserted finite-type
algebra. This avoids introducing a second scalar-action instance on the
degree-zero submodule.

`projectiveSpaceToSpec_isProper` proves properness of the actual
`projectiveSpaceToSpec R n`. Mathlib's
`AlgebraicGeometry.Proj` construction is proper over the spectrum of the
degree-zero ring when the graded ring is of finite type over it. The
remaining factor in the published structural morphism is the spectrum of
the constants isomorphism, so it is an isomorphism and the composite is
proper. Consequently Mathlib also supplies separatedness and local finite
type for this morphism.

The provenance is derived/internal: the module adapts Mathlib's
`ProjectiveSpectrum/Proper.lean` theorem to the project's existing finite
polynomial construction. It introduces no projective-map, line-bundle
separation or closed-immersion criterion.
