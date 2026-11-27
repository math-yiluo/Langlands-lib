# Symmetric wave-packet translation from the one-packet norm bound

`wavePacketTranslationNormBoundReduction` proves
`WavePacketTranslationNormBoundReductionStatement`. Its inputs are
`NormalizedConvolutionImaginarySpanStatement`, `EisensteinMeromorphicContinuationStatement`,
`EisensteinRootHyperplaneStatement`, `IntertwiningSquareIntegrableExpansionStatement`,
and `LocalWavePacketNormBoundStatement`. Its conclusion is `WavePacketTranslationStatement`
for the supplied presented parabolics, compact subgroup, imaginary intertwining operators,
and full rational quotient with its Haar measure.

`memLp_rightConvolution_rationalQuotient` starts with a continuous left rational-invariant
function whose descent is in \(L^2\). The descent is continuous, and the quotient right
action makes its right translates a jointly measurable family. Every translate has the
same squared integral by right invariance of the quotient measure. The estimate
`integrable_sq_norm_kernelIntegral` applies Cauchy–Schwarz with the absolute value of the
kernel as a Haar density and uses Tonelli's theorem to show that the integrated family
is in \(L^2\). Evaluation on quotient representatives identifies this family integral
with right convolution on the adelic group.

`wavePacketTranslation_of_convolution_of_localNormBound` applies the local norm bound
at each of the supplied parabolics. The union of the supports of its finitely many
coefficients is compact, and its image on the imaginary axis belongs to the supplied
holomorphy domain. Thus each packet is in \(L^2\), as is their sum with the prescribed
reciprocal Weyl-set weights. The convolution estimate gives \(L^2\) membership for
every left-finite convolution of that sum. The right-translation separation theorem
and `leftFiniteConvolutionApproximation` give a single convolution within the prescribed
error. Symmetric convolution stability represents the convolution by a new finite
packet in the same supplied symmetric space.

The reduction also extends the local norm bound to bounded coefficients via
`boundedWavePacketNormBound_of_local`. This bound, joint root-hyperplane control obtained
from the given meromorphic continuation and root-hyperplane statement, and existence
of compatible measures give imaginary-axis holomorphy. The finite convolution assembly
then supplies the symmetric convolution stability used in the approximation step.

## Sources

The integrated right action and the symmetric packet construction use J. Arthur,
*An introduction to the trace formula*, §7, printed pp. 32–35 (volume PDF pp. 44–47),
registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`. The local norm
bound is the smooth case of (19) in E. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series*, §8, Lemma 10, printed p. 329 (volume PDF p. 338).
The proof of Proposition 6 on pp. 329–330 uses this bound for imaginary-axis holomorphy.
The volume is registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`,
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
The implication here combines those estimates with the convolution and separation arguments
on the full rational quotient.
