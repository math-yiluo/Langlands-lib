# Cuspidal spectral rigidity over totally complex number fields

`Langlands.Automorphic.Unramified.cuspidalSpectralRigidityTC` proves
`CuspidalSpectralRigidityTCStatement.{uF, uV}`, with independent universes for
the number field and the presentation carriers. The three conjuncts give
independence of the positive power traces of distinct cuspidal classes and
recovery of the constituents, with multiplicities, from either cofinite
power traces or cofinite Euler polynomials.
[Statement](CuspidalSpectralRigidityTCStatement.md)

## Proof

For a totally complex field \(F\),
`infiniteWhittakerSliceModelAt_of_isTotallyComplex` supplies the adelic
Whittaker slice model. The theorem
`specifiedWhittakerSliceComparisonAt_of_complex` uses
`complexPlaceWhittakerRestrictionSurjectivity` to identify the slice ranges
with the prescribed local Whittaker models at each infinite place, for the
additive character and its inverse.

The theorem `cuspidalPairNormalizedContinuationTCAt_of_local` applies the
ordinary Rankin–Selberg tests on these ranges.
`complexOrdinaryNormalizedAllGrowth` supplies entire continuation and
exponential growth on vertical strips for the normalized local integrals.
`complexOrdinaryNormalizedGeneration` supplies the nonvanishing normalized
tests needed to construct the completed continuation. The real-place index
type is empty over \(F\).
[Local-test construction](../../Global/Factors/CuspidalPairPoleFromLocalTests.md)

The theorem `cuspidalSpectralRigidityTC_of_normalizedContinuation` obtains
the completed simple pole profile using standard finite pair \(L\)-data and
complex-place parameters. It takes absolute convergence from the self-pair
continuation proof and cancels the archimedean and omitted finite factors
to continue the partial pair \(L\)-functions. Landau's argument with
squared power traces gives the logarithmic limits at \(s=1\). In a trace
relation, the independence reduction pairs with the conjugate of a
norm-power-normalized constituent of minimal real twist exponent among
the nonzero coefficients. The logarithmic limit isolates that coefficient.
The recovery reduction groups the two lists by cuspidal class and applies
independence to the differences of multiplicities. Equality of Euler
polynomials gives equality of power traces via their reciprocal roots.
[Pole-profile reduction](CuspidalSpectralRigidityTCPoleProfileReduction.md)

## Sources

- H. Jacquet and J. A. Shalika, *On Euler Products and the Classification
  of Automorphic Forms II* (1981), §4.1 and Theorem 4.2, printed pp. 805–807
  (PDF pp. 30–32), and the numerical step in the proof of Theorem 4.4,
  printed p. 809 (PDF p. 34). Registered source `jacquet-shalika-1981-euler-ii`.
  SHA-256 `4d3f68841a558631a1624482d497665c2b52059bb9e0b7333948b8d1610b57d8`.
- H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Theorems 2.1,
  2.3, 2.6 and 2.7 and Remark 2.2, author-posted pp. 6–10, for the complex
  ordinary local inputs. Registered source `jacquet-2009-archimedean-rankin-selberg`.
  SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024),
  equation (11.23) and Theorem 11.7.1, printed pp. 308–309 (PDF pp. 319–320),
  for the completed product and pole normalization. Registered source
  `getz-hahn-2024-automorphic-representations`.
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
