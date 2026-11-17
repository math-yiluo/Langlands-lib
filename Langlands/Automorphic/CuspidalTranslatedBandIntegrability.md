# Integrability of translated cusp functions on the determinant band

For every number field in an arbitrary universe with the existing compact
`AdeleQuotient` convention, every natural matrix rank, and any actual cuspidal
operator realization, this internal result keeps the canonical rational quotient
Haar measure restricted to `1 < |det| < 2`.

`memLp_translate_of_cuspidal` proves that every fixed actual adelic right translate
of an original vector is square integrable on that same band. It uses the actual
continuous quotient function, without requiring the translated function to belong
to the original compact-finite operator realization. No irreducibility, positive
rank or unitary central character is assumed.

The proof applies the published uniform band-cover theorem with the singleton
compact translation set `{a}`. The continuous norm of the translated quotient
function satisfies its dominating bound exactly. The published
`memLp_band_of_continuous` converts the covering estimate to band square
integrability of the norm, hence of the complex function.

`integrable_inner_translate_of_cuspidal` pairs this function against any vector of
the full actual band `Lp ℂ 2` space. The product of their norms is integrable by
the `L²` product estimate, and the pointwise inner-product norm bound proves
integrability of the scalar coefficient.

`CuspidalTranslatedBandIntegrabilityStatement` combines these two conclusions,
and `cuspidalTranslatedBandIntegrability` proves it. The provenance is internal
composition of `CuspidalUnitaryForm`'s published uniform covering and continuous
band-norm estimates with the standard `L²` product estimate. Despite that
module's name, the estimates used here require cuspidality and retain no unitary
central-character premise.

This result establishes the integrability input for actual determinant-band
Hilbert coefficients. It proves no coefficient smoothness, differential
covariance, invariance of the source's Hilbert closure, full archimedean action,
Whittaker uniqueness or unconditional operator multiplicity one.
