# Real Fourier exchange inside the split Godement kernel

This module is the real counterpart of the Library's `ComplexGapTailExchange`.

`LeftWhittakerEquivariant k q a W` says that `W : GL_{k+q+1}(ℝ) → ℂ` satisfies
`W (u g) = realWhittakerCharacter (-a) u · W g` for all upper unipotent `u`. Every vector of the
Library's real Whittaker model for `ψ_{-a}` has this property
(`RealLocalWhittaker.model_le_regularFunctions`). The complex module takes `W` in the complex Whittaker
model for `ψ_{-a}`; the real statement only uses this transformation law, so it applies to every
function with it.

A `SplitTailTest k q` consists of a function `leading` of the first `k` columns, a function `first`
of the first tail column, Schwartz column tests `later j` for the later columns and a function
`lastFrequency` of the last row of the inverse. For a character `χ : ℝˣ →* ℂ`, `g, h ∈ GL_k(ℝ)` and
`B ∈ GL_{k+q+1}(ℝ)`:

* `fixedTailFactor T W χ g h B` is the product of `leading` at the leading columns of `B · diag(h, 1)`,
  `first` at the first tail column of `B`, `lastFrequency` at the last row of `B^{-1}`,
  `W (diag(g h^{-1}, 1) · B^{-1})`, `χ(det h)` and `χ(det B)`;
* `ordinaryBlockTailKernel T W χ g h B (X, Z)` is, with `C = B · packedTail (laterRectangle X) Z`,
  `fixedTailFactor … C · ∏_j later_j (column k + j + 1 of C)`;
* `alternateBlockTailKernel a T W χ g h B Z` is, with `C = B · packedTail 0 Z`,
  `fixedTailFactor … C · ∏_j 𝓕_a later_j (column k + j of C^{-T})`, where `𝓕_a` is the positive real
  Fourier transform `realFourierTransform a`.

For fixed outer data, `packedTail` fixes the leading columns, the first tail column (when the first
rectangular column vanishes), the last row of the inverse and the determinant. Conjugating the inverse
upper block by the embedded leading matrix keeps the first rectangular column zero, so by the
transformation law the Whittaker factor acquires the standard tail character at `a`. This gives
`fixedTailFactor (B · packedTail Y Z) = fixedTailFactor B · ψ_a(Z)`; for `Z = 1` the factor is
invariant (`fixedTailFactor_mul_laterRectangle`). Hence the ordinary kernel is
`fixedTailFactor B · triangularOrdinary a B later` and the alternate kernel is
`fixedTailFactor B · triangularFourier a B later` (`alternateKernel_eq`).

`RealGapTailExchangeStatement` (proved by `realGapTailExchange`): for `a : ℝˣ`, a split test `T`, a
function `W` with `LeftWhittakerEquivariant k q a W`, `χ`, `g`, `h` and `B`, with
`μ = realSelfDualMeasure a`, the ordinary kernel is integrable for the product of the rectangular
measure and `entryHaar μ (q + 1)`, the alternate kernel is integrable for `entryHaar μ (q + 1)`, and
the integral of the ordinary kernel is `(|det B|^{-1})^q` times the integral of the alternate kernel. It
follows from `realGapTriangularFourier` after factoring out `fixedTailFactor B`.

This is the identity for fixed outer data behind (10.4) and (10.5).
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
