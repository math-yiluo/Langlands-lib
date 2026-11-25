# Exactness of the Čech model in degree one from vanishing `H¹`

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule`.

- `exact_of_isZero_H1`: let `π` be separated and `C` a Čech representative of a line bundle `L`.
  If `H¹(X_A, L_A) = 0` (the Library's `relativeCohomology` in degree one), then every
  `x ∈ A ⊗ K₁` with `(1 ⊗ δ₁) x = 0` lies in the image of `1 ⊗ δ`. Indeed `Θ₁ x` is a Čech
  `1`-cocycle; Čech `H¹` of the cover is `H¹(X_A, L_A)` (the bridge
  `Modules.CechBridge.hsuccEquivRelativeCohomology`, for quasi-coherent `L_A`), so it is a
  coboundary, and `CechRep.Θ₁_exact` gives the preimage.

## Source

Kleiman, *The Picard scheme*, Subsection 3.10 (p.25), condition (v) `H¹(X_s, F_s) = 0`, used at
every point.
