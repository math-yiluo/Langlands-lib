# Splitting matrix algebras over a quaternion algebra with involution

This internal module builds on `Quaternionic.SplittingChart`. It carries the splitting of a
`K`-algebra `D` (a chart `e : L ⊗[K] D ≃ₐ[L] M₂(L)`) over to the matrix algebra `M_n(D)`, on
which the unitary and symplectic groups of `Quaternionic.GroupSchemes` are defined. It turns
the defining equation `u H ᵗu^σ = H` of the unitary group into the equation `g C gᵀ = C` of
the isometry group of an alternating matrix `C`. It also shows that the reduced norm becomes
the determinant.

## The matrix chart

Let `R` be a commutative ring with compatible `K`- and `L`-algebra structures.

* `blockChartR e R : R ⊗[K] M_n(D) ≃+* M_n(M₂(R))`: first the Library's
  `FiniteAlgebraUnits.MatrixPoints.coefficientEquiv` (`R ⊗[K] M_n(D) ≃ M_n(R ⊗[K] D)`), then
  `chartR e R` entrywise.
* `matrixChartR e R : R ⊗[K] M_n(D) ≃+* M_{n × 2}(R)`: then Mathlib's block-matrix
  flattening `Matrix.compRingEquiv`.
* `matrixChartR_apply`, `matrixChartR_tmul_apply`: entry formulas. The `((i, a), (j, b))` entry
  of the chart of `r ⊗ M` is `r · e(1 ⊗ M_{ij})_{ab}`.
* `matrixChartR_naturality`: compatibility with `L`-algebra maps `R → R'`.
  `matrixChartR_one_tmul`: the chart of a constant `1 ⊗ M` over `R` is its chart over `L`
  with entries mapped into `R`.

## The involution

* `coefficientEquiv_baseChange`: for the conjugate transpose `τ = σ.matrix n`, the entries of
  `τ_R x` are `(τ_R x)_{ij} = σ_R (x_{ji})`.
* `blockInvolutionMatrix e σ` (written `S̃`) and `blockInvolutionMatrixInv e σ` are the
  block-diagonal matrices with blocks `S` and `S⁻¹`, where `S = σ.involutionMatrix e`.
  `blockInvolutionMatrix_mul_inv` and `blockInvolutionMatrix_inv_mul` show they are inverse.
  `transpose_blockInvolutionMatrix`: `S̃ᵀ = S̃` when `σ.symmetricSubspace` has dimension `3`
  (from `involutionMatrix_transpose`).
* `matrixChartR_baseChange`: `Φ(τ_R x) = S̃ Φ(x)ᵀ S̃⁻¹` with `Φ = matrixChartR e R`. This
  follows blockwise from `chartR_baseChange`. `matrixChartL_baseChange` is the case `R = L`.

## The reduced norm

* `matrixChartL e : L ⊗[K] M_n(D) ≃ₐ[L] M_{n × 2}(L)` is `matrixChartR e L` as an
  `L`-algebra isomorphism. `splittingMap_matrixChartL`: its extension to `R` (the Library's
  `ReducedNorm.splittingMap`) is `matrixChartR e R`.
* `reducedNorm_eq_det_matrixChartR`: for central `D` and nonempty `n`,
  `CentralSimple.reducedNorm K (M_n(D)) R x = det (matrixChartR e R x)`. This is the Library's
  `CentralSimple.reducedNorm_eq_det_fintype`, which holds for any finite matrix chart.

## The alternating Gram matrix

* `IsAntihermitian.exists_eq_sub`: a trace-valued antihermitian `H` (`ᵗH^σ = -H`, diagonal
  entries `a - σ a`) is `V - ᵗV^σ`. Take `V` to be `H` strictly above the diagonal (for an
  enumeration of the indices), `a_i` on the diagonal, and `0` below it.
* `splitGram e σ H = Φ(1 ⊗ H) S̃` (written `C`) is the split Gram matrix over `L`.
* `exists_splitGram_eq_sub`: if `σ.symmetricSubspace` has dimension `3` and `H` is
  antihermitian, then `C = W - Wᵀ` with `W = Φ(1 ⊗ V) S̃`. Indeed
  `Φ(1 ⊗ H) = Φ(1 ⊗ V) - S̃ Φ(1 ⊗ V)ᵀ S̃⁻¹`, and `S̃ᵀ = S̃`. Consequently
  `transpose_splitGram` (`Cᵀ = -C`) and `splitGram_diag` (zero diagonal) hold in every
  characteristic.
* `det_splitGram_ne_zero`: `C` is invertible when `H` is.
* `mul_mul_baseChange_eq_iff`: for `u ∈ R ⊗[K] M_n(D)`,
  `u (1 ⊗ H) τ_R(u) = 1 ⊗ H ↔ g C gᵀ = C` with `g = Φ u` and `C` mapped into `R`. Apply the
  ring isomorphism `Φ` and the involution formula. Then multiply on the right by `S̃` or by
  `S̃⁻¹`.

## Provenance

These are standard identifications. Over a splitting field, the hermitian or antihermitian
form becomes a bilinear form of twice the size, and the reduced norm becomes the determinant.
The proofs are direct matrix computations written for this module. They use the Library's
`coefficientEquiv` and `reducedNorm_eq_det_fintype` and Mathlib's `Matrix.comp`.
