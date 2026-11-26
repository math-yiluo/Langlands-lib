# Rectangular two-block coordinates for real general linear Haar measure

Fix `0 < k < n` and the two-block shape `(k, n - k)`.

* `rectangleCoordinates` identifies the unipotent radical with the rectangle
  `Mat_{k × (n-k)}(ℝ)`; products become sums and inverses negatives
  (`rectangleCoordinates_mul`, `rectangleCoordinates_inv`).
* `upperRectangle X` is the upper unipotent matrix with off-diagonal block `X`.
* `leviBlocks` identifies the Levi factor with `GL_k(ℝ) × GL_{n-k}(ℝ)`, and
  `diagonalBlocks g₁ g₂` is the block diagonal matrix `diag(g₁, g₂)`.

`RealTwoBlockHaarStatement`: for an additive Haar measure `ν` on `ℝ`, arbitrary Haar measures
`μ` on `GL_n(ℝ)`, `μ₁` on `GL_k(ℝ)`, `μ₂` on `GL_{n-k}(ℝ)`, and a Haar measure `κ` on the
orthogonal group invariant under inversion, there is `c > 0` with

`μ = c • map ((((g₁, g₂), X), q) ↦ q · upperRectangle X · diag(g₁, g₂))
        (((μ₁ × μ₂) × rectangularMeasure ν k (n-k)) × κ)`.

`realTwoBlockHaar` proves it from the reversed-order case of `realParabolicHaar`: the
identifications transport `μ₁ × μ₂` and the rectangular product measure to Haar measures on the
Levi factor and the radical, which are invariant under inversion (Haar measures on real general
linear groups are inversion invariant, `RealGodement.realMatrixHaar_symmetries`, and the
rectangular measure is invariant under negation).

This is the real counterpart of the Library's `ComplexTwoBlockHaar`, with arbitrary Haar
measures on the general linear groups in place of the explicit complex density. The unweighted
formula in the coordinates `q · upperRectangle X · diag(g₁, g₂)` is a precursor of Jacquet's
coordinates `h = k (1, 0; 0, g₂)(1, Y; 0, 1)(h₁, 0; 0, 1)`, *Archimedean Rankin–Selberg Integrals*
(2009), §10.1: the substitution `Y = X g₂` turns it into the chart printed there, with the density
`|det g₂|^{-k}`; that step is proved in `RealTwoBlockRightHaar`.
