# The alternate split real Godement integral

This module is the real counterpart of the Library's `ComplexGapAlternateRestriction`. Let `k > 0`,
`q ≥ 0` and `n = k + q + 1`. The real Godement coefficient is
`RealJacquet.realAdjacentGodementCoefficient` on `GL_{n+1}(ℝ)` (see `RealGodementPaddedRestriction`).

* A `GodementColumnFactors k q` consists of a Schwartz function `leading` on real `n × k` matrices
  and Schwartz column tests `tail j` on `ℝ^n`, `j < q + 2`.
* `squareEval T A = leading(first k columns of A) · ∏_{j ≤ q} tail_j(column k + j of A)` for a square
  `n × n` matrix `A`. `eval T X = leading(first k columns of X) · ∏_{j < q+2} tail_j(column k + j of X)`
  for an `n × (n+1)` matrix `X`.
* `eval_joinLastColumn`: `eval T [A | x] = squareEval T A · tail_{q+1}(x)`. `joinLastColumn_split`:
  every `n × (n+1)` matrix is the join of its first `n` columns and its last column.
* `partial T a` is the split tail test of `RealGapTailExchange` with leading factor `leading`, first
  column factor `tail 0`, later factors `tail (j+1)` for `j < q`, and last-row factor
  `realFourierTransform a (tail (q+1))`.
* `restrictionWeight k q c x = η(x) |x|^{(k+q)/2}` as a character of `ℝˣ`, with `η` the character of
  `c`.
* `paddedRestrictionKernel_split`: on a chart point `B · packedTail (laterRectangle X) Z · diag(h, 1)`,
  the padded restriction kernel of `RealGodementPaddedRestriction` at `diag(g, 1)` and `b = 1`, for
  the square factor `squareEval T` and the last factor `tail (q+1)`, equals the ordinary split kernel
  `ordinaryBlockTailKernel (partial T a) U (restrictionWeight k q c) g h B (X, Z)`.
* `alternateRestrictionKernel a c T U g p Z = (|det R|^{-1})^q ·
  alternateBlockTailKernel a (partial T a) U (restrictionWeight k q c) g h R Z`, where `p` are the
  outer coordinates of `RealGapTriangularChart`, `h` their leading matrix and `R = retainedMatrix p`.

`RealGapAlternateRestrictionStatement` (proved by `realGapAlternateRestriction`): let `a ∈ ℝˣ`, `D'`
a real quotient measure datum of rank `k + q`, `η₁` a Haar measure on `GL_k(ℝ)` and `κ` an
inversion-invariant Haar measure on the orthogonal group. There is `C > 0` such that for every
character datum `c`, every `T`, every Schwartz `Φ` on `n × (n+1)` matrices with
`Φ([A | x]) = squareEval T A · tail_{q+1}(x)`, every `U ∈ realUniformWhittakerModel (k+q) ds (-a)`
and every `g ∈ GL_k(ℝ)`, with `μ = realSelfDualMeasure a`, `η = entryHaar μ (q+1)` and
`σ = outerMeasure k q μ η₁ κ`: each fiber `Z ↦ alternateRestrictionKernel … p Z` is integrable for `η`,
its integral is integrable in `p` for `σ`, and

`realAdjacentGodementCoefficient D' a Φ U c (diag(diag(g, 1_{q+1}), 1)) =
realAdjacentWeylSign (k+q) c · P g (1/2) · C · ∫ (∫ alternateRestrictionKernel … p Z dη(Z)) dσ(p)`.

The proof applies `realGodementPaddedRestriction` with `b = 1` to the separated test. Let `C` be the
retained matrix `B` times the packed tail. Then `C · diag(h, 1)` has the same tail columns as `C`, and
`diag(g h⁻¹, 1) · C⁻¹` has the same last row as `C⁻¹`; these identities make the padded kernel the
ordinary split kernel on each chart point. The constant `C` comes from
the triangular Haar formula `realGapTriangularChart` for `D'.groupHaar`, which pulls absolute
integrability back to the chart. Fubini's theorem and the fixed-data exchange `realGapTailExchange`
(applicable because vectors of the uniform model satisfy `LeftWhittakerEquivariant`) give the
alternate formula and the two integrability statements. This is Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §10.2, (10.4)–(10.5).
