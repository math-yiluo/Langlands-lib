# Row Fourier surjectivity under Haar rescaling

Worker 457 proves the published
`Langlands.HarmonicAnalysis.RowFourierHaarSurjectivityStatement` without
additional hypotheses. This is a derived proof of the conditional
normalization interface in `PadicRowFourierSurjectivityStatement`.
The supplied field, topology, Borel measurable space, character, reference
measure, and dimension remain the parameters of that statement.

Mathlib's regular additive Haar uniqueness theorem identifies the other
supplied scalar Haar measure as `ν.measure = c • μ.measure`, where
`c = Measure.addHaarScalarFactor ν.measure μ.measure : NNReal`.
The Haar positivity theorem proves `0 < c`. Its `NNReal` type also
ensures that the scalar is finite, so this equality has the required
orientation and neither a zero nor an infinite normalizing factor occurs.
Local compactness and second countability give sigma compactness, and
finiteness of Haar measure on compact sets then gives sigma-finiteness
of the reference measure.

`rowMeasure_scale` applies the published `rowCoordinateMeasure_scale` to
the constant coordinate family. Thus the actual row measure scales by
`(c : ENNReal)^d`. `rowFourierIntegral_scale` then applies Mathlib's
Bochner integral scaling theorem, converting this measure scalar to
`((c : ℝ) : ℂ)^d`. It holds for the raw integral with arbitrary functions;
the main argument uses actual Schwartz–Bruhat functions, whose integrands
are integrable by the published `rowFourierIntegrand_integrable`.

For a requested test function `Φ`, composition with the negation
homeomorphism supplies the test function `Φneg(x) = Φ(-x)`. The proof
uses preservation of local constancy under continuous precomposition
and preservation of compact support under a homeomorphism.
The assumed `RowFourierClosed` gives an actual test function `g` equal
to the transform of `Φneg`. The assumed `IsRowSelfDual`, applied
to `Φneg`, proves that the transform of `g` is `Φ`: its reflection is
`Φneg(-y) = Φ(y)`.

Write `a = ((c : ℝ) : ℂ)^d`. Positivity of `c` proves `a ≠ 0`.
The kernel is the test function `a⁻¹ • g`. The measure scaling identity
and the published complex linear map `rowFourierTransform` give its
transform for `ν` as `a * (a⁻¹ * Φ(y)) = Φ(y)`, pointwise. Throughout,
the pairing and integral retain the published plus sign with no
conjugation. The proof is uniform in `d`; at `d = 0`, the empty product
and `c^0` both equal one.

The mathematical provenance is the derived normalization argument already
documented in the target's paired Markdown. This module makes no new
claim about the cited originals. It constructs no self-dual measure and
does not derive row inversion from scalar inversion. Scalar self-dual
existence and row compatibility remain separate obligations.
