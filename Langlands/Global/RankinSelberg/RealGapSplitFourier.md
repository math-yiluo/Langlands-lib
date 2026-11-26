# Fourier transformation of the split real Godement test

This module is the real counterpart of the Library's `ComplexGapSplitFourier`. Let `n = k + q + 1`
and let `T` be `GodementColumnFactors k q` (see `RealGapAlternateRestriction`). For `a ∈ ℝˣ`,
`realRectangularSchwartzFourier a` is the Library's Fourier transform of Schwartz functions on real
matrices, `Φ ↦ (Y ↦ ∫ Φ(X) ψ_a(∑_{i,j} X_{ij} Y_{ij}) dX)` for the scaled character
`ψ_a = realScaledCharacter a` and the product of the self-dual measures `realSelfDualMeasure a`.

* `fourierFactors k q a T` has leading factor `realRectangularSchwartzFourier a T.leading` and tail
  factors `RealGapColumnFourier.columnSchwartzFourier a (T.tail j)`.

`RealGapSplitFourierStatement` (proved by `realGapSplitFourier`): for every `a`, every Schwartz
function `F` on real `n × n` matrices with `F A = squareEval T A` for all `A`, and every `A`,

`realRectangularSchwartzFourier a F A = squareEval (fourierFactors k q a T) A`.

The proof splits a square matrix into its first `k` columns and its remaining `q + 1` columns. This
splitting is a measurable equivalence carrying the rectangular product measure to the product of the
rectangular measure on `n × k` matrices and one row measure on `ℝ^n` for each tail column, by
transposition (`measurePreserving_transpose_rectangularMeasure`) and reindexing of the coordinates.
The trace pairing splits as the sum of the pairing of the leading blocks and the column dot
products, and the character turns this sum into a product. The integral of the resulting product
function is the product of the integrals (Fubini's theorem and `integral_fintype_prod_eq_prod`), which
are the transforms of the individual factors. This is the factorization of the Fourier transform of a
separated test used in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
