# Ordinary and dual real Godement restrictions with one Haar constant

This module is the real counterpart of the Library's `ComplexGapNormalizedRestriction`. Notation as in
`RealGapWeylRestriction`, `RealGapUnitDeterminant` and `RealGapMatchedTests`; `n = k + q + 1`,
`pad = diag(·, 1)` from `GL_n(ℝ)` to `GL_{n+1}(ℝ)`.

* `unitOrdinaryKernel a c T U g p Z` is the alternate tail kernel of `RealGapTailExchange` for the
  reversed factors `reverseTail T`, the character `restrictionWeight k q c`, the leading matrix of `p`
  and the normalized retained matrix `unitRetained p`.
* `unitDualKernel a c F T Ud g X (p, (V, Z))` is `dualFiber a c F T Ud g h (retainedTail p Z) V X`, with `h`
  the leading matrix of `p`.

`RealGapNormalizedRestrictionStatement` (proved by `realGapNormalizedRestriction`): let `0 < k`,
`a ∈ ℝˣ`, `D'` a real quotient measure datum of rank `k + q`, `η₁` a Haar measure on `GL_k(ℝ)` and `κ` an
inversion-invariant Haar measure on the orthogonal group. With `μ = realSelfDualMeasure a`,
`η = entryHaar μ (q+1)` and `σ = unitOuterMeasure k q μ η₁ κ`, there is one `C > 0` such that:

1. for every test `Φ` with `Φ([B | x]) = squareEval T B · T.tail_{q+1}(x)`, every
   `U ∈ realUniformWhittakerModel (k+q) ds (−a)` and `g ∈ GL_k(ℝ)`, the fiber integral
   `p ↦ ∫ unitOrdinaryKernel a c T U g p Z dη(Z)` is integrable for `σ` and
   `realAdjacentGodementCoefficient D' a Φ U c (pad(A g) · tailWeyl k (q+2)) =
   η_c(det w_{q+2}) · realAdjacentWeylSign (k+q) c · P g (1/2) · C · ∫∫ unitOrdinaryKernel …`;
2. for every Schwartz `F` with `F = squareEval T`, every `Ud ∈ realUniformWhittakerModel (k+q) ds a`,
   `g` and `(q+1) × k` matrix `X`, the kernel `unitDualKernel a c F T Ud g X` is integrable for
   `σ × (rectangularMeasure μ q k × η)` and
   `realAdjacentGodementCoefficient D' (−a) (realColumnProduct F̂ f̂) Ud c⁻¹ (pad(A g · lowerShear X)) =
   realAdjacentWeylSign (k+q) c⁻¹ · P g (1/2) · C · ∫ unitDualKernel a c F T Ud g X`,
   where `F̂ = realRectangularSchwartzFourier a F` and `f̂ = realRowSchwartzFourier a (T.tail_{q+1})`.

Here `η_c` is the character of `c` and `P g s = |det g|^s`. The constant `C` comes from
`realGapDualChart` for `D'.groupHaar`, which gives the same constant for the normalized chart and the
dual chart. The ordinary part moves `tailWeyl k (q+2)` into the test
(`realAdjacentGodementCoefficient_mul_right`, `rectangularTranslate_tailWeyl`) and applies
`realGodementPaddedRestriction`. It pulls the padded kernel back to the normalized chart and identifies
each fiber with the ordinary split kernel (`paddedRestrictionKernel_split`). The tail exchange
`realGapTailExchange` has determinant factor one there, because `|det(unitRetained p)| = 1`. The dual part applies
`realGodementPaddedRestriction` at `−a` to the separated transformed test with `b = lowerShear X`, whose
determinant is one, and pulls back along the dual chart. This is the pair of restrictions of Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §§10.2–10.3.
