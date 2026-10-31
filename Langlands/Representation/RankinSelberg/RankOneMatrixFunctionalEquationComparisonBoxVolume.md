# The explicit positive volume in the original box extraction

Worker 396. Internal derived prerequisite for the matrix functional-equation
comparison. The field and representation-carrier universes remain independent.
This module exposes the actual volume factor from the published box integration
calculation so that a later paired calculation can identify the same scalar.

`boxComparisonVolume F n A q a` is the real product of three masses: the
normalized general-linear Haar measure, restricted to the integral subgroup,
of `boxSupport`; the tail measure of `torusBox`; and the normalized unipotent
Haar measure of `unipotentBox`. Its positivity theorem assumes `A >= 0`,
`q <= 0` and positive principal level `a`. Each mass is finite and strictly
positive by the published box mass lemmas, so their real product is positive.

`OriginalBoxVolumeComparison` packages positivity of this specified real volume
and `OriginalMatrixBlockComparison` with its complex cast. The test is exactly
the compact-open box indicator, and the coefficient is a specified actual
bi-smooth coefficient of the given model representation. The original block
integral, canonical constant-one second vector, supplied additive Haar measure
and quotient measure are those of `OriginalMatrixBlockComparison`.

`box_matrixIntegral_eq_volume_mul` proves the precise factor in the box integral
identity whenever the matrix integrand is integrable. It uses the published
Iwasawa integration theorem over the actual box support. On that support, the
principal-level stabilizer and box reparametrization give a measure-preserving
right shift of the Iwasawa parameters; off it the integrand vanishes. At an
Iwasawa point the integrand separates into the rank-one determinant term, the
tail-torus indicator and the unipotent-box indicator. Product integration
extracts the latter two masses. The density of the rank-one part of the Iwasawa
measure converts the shifted determinant exponent to the actual rank-one model
integrand. Real scalar multiplication and multiplication in the complex field
then give exactly the displayed three-volume product. This proof uses the
Bochner identities directly; it does not identify a scalar by cancelling a
possibly zero integral.

`originalBoxVolumeComparison_of_eq_on_box` uses the actual model's common matrix
convergence half-plane for an actual coefficient agreeing with the model
function on the box. Equality of complete cutoff-weighted integrands transfers
integrability and values to the model function. The preceding explicit-volume
identity and the literal original block-zero/rank-one equality give the desired
comparison on that half-plane for every compatible quotient measure.

`exists_originalBoxVolumeComparison` chooses the box and normalized actual
averaged coefficient as in the published box choice theorem. It keeps all
`ModelBoxConditions`, the compact open subgroup and its compactness witness,
left invariance of the box test, determinant norm one on the subgroup and
pointwise coefficient equality on the box. The resulting original comparison
uses the explicit volume rather than an unspecified positive scalar.

The module is derived from published box reparametrization, support and product
integration, matrix convergence and the literal original block identification;
it is not a new source transcription. It adds no self-duality, irreducibility,
finite-length, nonzero-functional or separate rank-one analytic premise. The
genuine dual comparison and the host task's exact all-rank theorem remain open.
