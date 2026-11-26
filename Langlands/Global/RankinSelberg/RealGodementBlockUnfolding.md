# The quotient change of variables in the real Godement block integral

This module is the real counterpart of the Library's `ComplexGodementBlockUnfolding`. Notation as in
`RealGodementTwoBlockRestriction` and `RealGodementLowerRectangle` with `k = t + 1`, `t < r`.

* `ComplexGodementBlockUnfolding.quotientShift H k hk` is the measurable equivalence `(x, p) ↦ (x · k(p), p)` of `H\A × S`, for a
  subgroup `H` of a topological group `A` with Borel σ-algebra, Borel σ-algebra on the quotient
  `H\A`, a second countable quotient, a measurable space `S` and a measurable map `k : S → A`.
  `ComplexGodementBlockUnfolding.measurePreserving_quotientShift`: if the quotient measure `τ` and the parameter measure `ρ` are both
  s-finite and every right translation preserves `τ`, the shift preserves `τ × ρ`. Both s-finiteness
  assumptions are used to exchange the order of integration.
* `beforeBlockKernel h c a F f U V z (x, X, p)` is the two-block kernel of `RealGodementLowerRectangle`
  at `g = x.out` and `b = lowerRectangle h X`, times `V(g) P g (z - (r-t)/2)`.
* `blockUnfoldedKernel h c a F f U V z (x, X, p)`, with `h₁ = p.1.1.1`,
  `h₂ = rightTail w Y v` and `A = diag(h₁, 1)`, is
  `F(h₂ A · lowerRectangle h X) · f̂_a(lastRow h₂⁻¹) · η(det h₂) P h₂ (r/2) ·
  η(det h₁) P h₁ (r/2) P h₁ (z - (r-t)/2) · realUnequalIntegrand h (ρ(h₂⁻¹) U) (ρ(h₁) V) z x`,
  where `ρ(·)` is right translation and `realUnequalIntegrand` is the Library's integrand of the
  real unequal-rank zeta integral.
* `blockUnfoldedKernel_shift`: if `U` has left character `ψ_{-a}` and `V` has left character
  `ψ_a`, then `beforeBlockKernel` is `blockUnfoldedKernel` composed with the inverse of the shift
  of the quotient coordinate by `h₁`.

`RealGodementBlockUnfoldingStatement` (proved by `realGodementBlockUnfolding`): let `D` and `D'` be
real quotient measure data of ranks `t` and `r`, `ν`, `νX` additive Haar measures on `ℝ`, `μ₁`, `μ₂`
Haar measures and `κ` an inversion-invariant Haar measure on the orthogonal group. There is `C > 0`
such that for every test `Φ` separated by `F` and `f`, every
`U ∈ realUniformWhittakerModel r ds (-a)`, every `V` with left character `ψ_a`, and every `z ∈ ℂ`:
if `blockUnfoldedKernel h c a F f U V z` is integrable for `D.measure × (rectangularMeasure νX × rightTailProductMeasure)`, then

`blockIntegral realNormalizedAbs D.measure νX (realAdjacentGodementCoefficient D' a Φ U c) V z =
(realAdjacentWeylSign r c · C) · ∫∫ blockUnfoldedKernel h c a F f U V z (x, u) dx du`,

the inner integral over the quotient. Joint integrability is a hypothesis of the statement.

The proof evaluates each point of the block integral by `realGodementLowerRectangle`. It combines
the half power of `det g` with the zeta power, `1/2 + (z - (r+1-t)/2) = z - (r-t)/2`. The right shift of
the quotient variable by the embedded first block preserves the product measure, by the right
invariance of the compatible quotient measure. It removes `h₁⁻¹` from the first Whittaker argument
and inserts `h₁` as a right translation of `V`; the opposite left characters justify evaluation at the
shifted representative. Fubini's theorem then exchanges the integrals. This implements the quotient
change in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.3.
