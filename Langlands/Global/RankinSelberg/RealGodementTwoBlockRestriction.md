# Two-block restriction of the real Godement coefficient

This module is the real counterpart of the Library's `ComplexGodementTwoBlockRestriction`. Notation
as in `RealGodementPaddedRestriction` and `RealTwoBlockRightHaar`: for `0 < k < r + 1` the
right-tail coordinates are `p = (((h₁, w), Y), v)` with `h₁ ∈ GL_k(ℝ)`, `w ∈ GL_{r+1-k}(ℝ)`, a
`k × (r+1-k)` real rectangle `Y` and `v` in the orthogonal group, and
`rightTail w Y v = v · diag(1, w) · upperRectangle Y`.

* `rightTailProductMeasure (r+1) k ν μ₁ μ₂ κ` is the product
  `((μ₁ × μ₂) × rectangularMeasure ν k (r+1-k)) × κ` with the density
  `rightTailWeight w = |det w|^{-k}`.
* `twoBlockRestrictionKernel hk hkn c a F f U g b p`, with `h₂ = rightTail w Y v`, is
  `F(h₂ diag(h₁, 1) b) · f̂_a(lastRow h₂⁻¹) · U(diag(g h₁⁻¹, 1) h₂⁻¹) ·
  η(det h₁) P h₁ (r/2) · η(det h₂) P h₂ (r/2)`.
* `twoBlockRestrictionKernel_chart`: this kernel is the padded restriction kernel of
  `RealGodementPaddedRestriction` at `diag(g, 1)` and `b`, evaluated at the chart point
  `h₂ · diag(h₁, 1)`.

`RealGodementTwoBlockRestrictionStatement` (proved by `realGodementTwoBlockRestriction`): let
`0 < k < r + 1`, `ν` an additive Haar measure on `ℝ`, `μ₁`, `μ₂` Haar measures on `GL_k(ℝ)` and
`GL_{r+1-k}(ℝ)`, `κ` an inversion-invariant Haar measure on the orthogonal group, and `D` a real
quotient measure datum of rank `r`. There is `C > 0` such that for every test `Φ` separated by `F`
and `f`, every `U ∈ realUniformWhittakerModel r ds (-a)`, `g ∈ GL_k(ℝ)` and `b ∈ GL_{r+1}(ℝ)`, the
two-block kernel is integrable for `rightTailProductMeasure` and

`realAdjacentGodementCoefficient D a Φ U c (diag(diag(g, 1) b, 1)) =
realAdjacentWeylSign r c · η(det b) · P b ((r+1)/2) · P g (1/2) · C · ∫ twoBlockRestrictionKernel … p dp`.

The proof takes the chart constant `C` from `realTwoBlockRightHaar` applied to `D.groupHaar`, so that
`D.groupHaar` is `C` times the pushforward of `rightTailProductMeasure` along the chart. It
transports the integrability and the integral of the padded kernel given by
`realGodementPaddedRestriction`. The determinant of the padded smaller matrix `diag(g, 1)` equals
`det g`. This is the two-block integral of Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§§9.1 and 10.1.
