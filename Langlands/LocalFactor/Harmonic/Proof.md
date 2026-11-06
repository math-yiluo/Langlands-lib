# The complete p-adic harmonic-analysis theorem

Worker 1786 proves `Langlands.LocalFactors.padicHarmonicAnalysis` of
exactly `Langlands.LocalFactors.PadicHarmonicAnalysisStatement.{u}` in
`Langlands.LocalFactor.Harmonic.Statement`. It has no parameters or
hypotheses beyond that universe-polymorphic proposition's full telescope.
The statement and its imported definitions are preserved.

The proof constructs the five-part conjunction from the following theorems:

| Component | Theorem |
| --- | --- |
| Fourier closure and integrability | `Langlands.HarmonicAnalysis.padicFourierClosure` |
| Dual and self-dual measure existence, uniqueness, inversion and symmetry | `Langlands.LocalFactors.padicFourierDuality` |
| Haar, character and test-function scaling | `Langlands.HarmonicAnalysis.padicFourierScaling` |
| Additive-conductor existence, scaling and integer-ring annihilator | `Langlands.HarmonicAnalysis.padicAdditiveConductor` |
| Dual and self-dual volume criteria, indicator transform, corrected Haar ratio and self-dual character scaling | `Langlands.LocalFactors.padicFourierNormalization` |

Each theorem proves its corresponding existing proposition with the actual
field, supplied topology, Borel measures and Fourier integrals of the target.
Normalization is proved in
[`NormalizationProof.md`](NormalizationProof.md) by the lattice indicator
transform, Haar proportionality, dual-measure existence and conductor scaling.
It is a proved conjunct in this assembly.

This is an internal assembly of those proofs. The original mathematical
sources and conventions are documented in
[`Statement.md`](Statement.md); the implementation routes for the other
four components are recorded in the imported proof modules' paired Markdown.
This module adds no mathematical assumptions.
