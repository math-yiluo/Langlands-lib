# Proof of the actual Haar inversion densities

`Langlands.Haar.haarInversionDensity` proves the exact published proposition
`Langlands.Haar.HaarInversionDensityStatement`, with arbitrary group universe
`uG`. For every actual left Haar measure `μ` on a locally compact Hausdorff
second countable Borel topological group, it proves

\[
\mu^{\mathrm{inv}}=\mu.\mathrm{withDensity}(\Delta),\qquad
\mu=\mu^{\mathrm{inv}}.\mathrm{withDensity}(g\mapsto\Delta(g^{-1})),
\]

where `Δ` is Mathlib's actual positive modular character, coerced to
`ℝ≥0∞`. The theorem has exactly the named proposition constant as its type,
with no additional outer premises. Worker 116 authored the complete Lean
proof; Worker 1643 adopted it unchanged and prepared the submission and
this revised documentation.

The proof weights a left Haar measure by Mathlib's positive modular character,
proves right invariance by transporting the density under right translations,
and applies left Haar uniqueness to the inverse weighted measure.
Transport under inversion and reciprocal modular values give a nonnegative
comparison scalar whose square is one. Evaluating the resulting measure
equality on a compact identity neighborhood with finite positive Haar mass
justifies cancellation, and nonnegativity forces the scalar to be one.
Multiplication of reciprocal densities gives the second measure equality.
Second countability supplies the regularity needed for Haar uniqueness.

The general modular continuity result is imported from the current Library.
It gives measurability of the density and local finiteness of the weighted
measure. Density transport reuses the published
`Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv`,
which follows from the measurable-embedding restriction and lower-integral
change-of-variables theorems. The duplicate private transport lemma was
removed during integration; the Haar argument and its conclusion are unchanged.

The provenance is internal: the proof combines the published modular
continuity theorem with pinned Mathlib density transport, modular-character
identities and Haar uniqueness. The source convention is recorded in the
unchanged target's paired Markdown. Smooth weights, actual right Haar
approximation operators, compactness, concrete automorphic Hilbert realization
and spectral decomposition remain separate obligations.
