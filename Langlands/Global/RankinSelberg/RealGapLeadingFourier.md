# Real Fourier exchange for the leading rectangle

This module is the real counterpart of the Library's `ComplexGapLeadingFourier`. Real matrices carry
the operator (row-sum) norm `Matrix.Norms.Operator`, the convention of the Library's real rectangular
Fourier transform `RealGodement.realRectangularSchwartzFourier`; the complex module uses the entrywise
norm.

* `rectFourier a Φ Y = ∫ Φ(X) ψ_a(∑_{i,j} X_{ij} Y_{ij}) dX` for the rectangular measure of
  `realSelfDualMeasure a`.
* `rectTransform a Φ` is the Library's `realRectangularSchwartzFourier a Φ`, and `rectTransform_apply`
  identifies its values with `rectFourier a Φ`.
* `pullRectangle g Φ X = Φ(g X)` for `g ∈ GL_n(ℝ)` (`pullRectangle_apply`), and
  `rectFourier_pullRectangle`: `rectFourier a (pullRectangle g Φ) Y = (|det g|^{-1})^l ·
  rectFourier a Φ (g^{-T} Y)` for `n × l` rectangles. The Jacobian comes from
  `Langlands.HarmonicAnalysis.haarMeasure_map_rectangular`.
* `stackRows k m l X Y` stacks a `k × l` and an `m × l` matrix (`stackRows_left`, `stackRows_right`), and
  `leadingRestriction k m l g Φ` is the Schwartz function `X ↦ Φ(g · stackRows X 0)`
  (`leadingRestriction_apply`); it is Schwartz because extension by zero rows is an injective linear map.
* `integrable_rectTransform_complement`: for every `H`, `Y ↦ rectTransform a Φ (g^{-T} · stackRows H Y)`
  is integrable for the rectangular measure on `m × l` matrices.

`RealGapLeadingFourierStatement` (proved by `realGapLeadingFourier`): for `a : ℝˣ`, `g ∈ GL_{k+m}(ℝ)`, a
Schwartz function `Φ` on `(k + m) × l` matrices and `H` a `k × l` matrix,

`rectFourier a (leadingRestriction g Φ) H = (|det g|^{-1})^l • ∫ rectTransform a Φ (g^{-T} · stackRows H Y) dY`.

The proof applies the Library's slice theorem `RealGodement.realGodementRectangularFourier` to the
partition of the entries into leading and complementary rows, with frequency `H` on the leading rows
and position `0` on the others, and transports both sides to rectangles by measure-preserving
reindexings; `rectFourier_pullRectangle` then moves the left multiplication to the Fourier variable.
The integrability statement is the same slice theorem for the exchanged partition, with zero
frequency, applied to `pullRectangle g^{-T} (rectTransform a Φ)`.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.3, passage from (10.9) to (10.10)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
