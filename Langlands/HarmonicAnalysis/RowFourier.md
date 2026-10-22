# Fourier integration on finite row spaces

Worker 11 authored this adapter in coordination with Worker 20, whose published
`Langlands.HarmonicAnalysis.Basic` supplies the character, test-function and
scalar Haar-measure types. The adapter does not replace those shared types.

For a supplied regular additive Haar measure `μ` on the field, `rowMeasure μ d`
is its actual product over `Fin d`. Its sigma-finiteness, additive Haar property
and finiteness on compact sets are proved under the displayed hypotheses.
`rowMeasure_entries` proves that a coordinate box has mass `μ(S)^d`;
dimension zero has unit point mass. No new scalar normalization is chosen.

The pairing is `rowPairing x y = ∑ i, x i * y i`. The Fourier integral uses
`ψ(∑ i, x i * y i)` with a plus sign, without conjugating either vector.
`rowFourierIntegrand_integrable` proves convergence for every actual compactly
supported locally constant complex test function: the pairing and character
are continuous, the kernel has continuous product with the test function, and
the support remains compact. `rowFourierTransform` is complex-linear from
the test-function space into the space of all functions, using additivity and
scalar compatibility of the integral.

`IsRowFourierPair ψ μ f g` requires both `f` and `g` to be actual
Schwartz--Bruhat functions and asserts pointwise equality of `g` with the
specified integral. The second function is proved unique. The construction
does not assume it always exists.

`RowFourierClosed` and `IsRowSelfDual` are explicit propositions for
preservation of the test space and Fourier inversion, respectively. Inversion
includes integrability of the second integral and the reflection `f(-y)`.
`RowFourierCompatibilityStatement` states that scalar self-duality gives both
properties in every finite dimension. It is a theorem target, not a proved
fact or a field in a structure. No self-dual measure or Fourier preservation
theorem is assumed to construct this module's objects.

The intended normalization comes from Jacquet, Piatetski-Shapiro and Shalika,
*Rankin--Selberg Convolutions* (1983), Section 0.3, printed page 378:
the matrix/row pairing, plus-sign Fourier integral and self-dual measure.
The row transform occurs in Theorem 2.7(iii), printed page 391.
Both pages were inspected visually in the original retained PDF
`C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The product-measure packaging and elementary integrability/linearity proofs
are derived implementations of these conventions. The finite-dimensional
compatibility proposition is a separate harmonic-analysis obligation;
this file does not supply its proof.

The only project import is the published `Langlands.HarmonicAnalysis.Basic`.
All remaining measure and topological facts used in construction are proved
Mathlib results.
