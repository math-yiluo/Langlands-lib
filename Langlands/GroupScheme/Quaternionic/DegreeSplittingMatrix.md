# Splitting matrix algebras over an algebra with involution, in any degree

Lean module: `Langlands.GroupScheme.Quaternionic.DegreeSplittingMatrix`
(namespace `Langlands.GroupScheme.Quaternionic.DegreeSplitting`).

This internal module builds on `DegreeSplittingChart`. It carries a chart
`e : L ⊗[K] D ≃ₐ[L] M_ι(L)` of a `K`-algebra `D` with an involution of the first kind `σ`
(`ι` a finite index type with decidable equality) over to the matrix algebra `M_n(D)`, on which
the unitary and symplectic groups of `Quaternionic.GroupSchemes` are defined. It turns the
defining equation `u H ᵗu^σ = H` of the unitary group into the equation `g C gᵀ = C` of the
isometry group of an alternating matrix `C`. It also shows that the reduced norm becomes the
determinant. It generalises the Library module `Quaternionic.SplittingMatrix`, which treats
`ι = Fin 2`, with the same definitions and proofs.

## The matrix chart

Let `R` be a commutative ring with compatible `K`- and `L`-algebra structures.

* `blockChartR e R : R ⊗[K] M_n(D) ≃+* M_n(M_ι(R))`: first the Library's
  `FiniteAlgebraUnits.MatrixPoints.coefficientEquiv` (`R ⊗[K] M_n(D) ≃ M_n(R ⊗[K] D)`), then
  `chartR e R` entrywise.
* `matrixChartR e R : R ⊗[K] M_n(D) ≃+* M_{n × ι}(R)`: then Mathlib's block-matrix
  flattening `Matrix.compRingEquiv`.
* `blockChartR_apply`, `matrixChartR_eq_comp`, `matrixChartR_apply`,
  `matrixChartR_tmul_apply`: unfolding and entry formulas. The `((i, a), (j, b))` entry of the
  chart of `r ⊗ M` is `r · e(1 ⊗ M_{ij})_{ab}`.
* `matrixChartR_naturality`: compatibility with `L`-algebra maps `R → R'`.
  `matrixChartR_one_tmul`: the chart of a constant `1 ⊗ M` over `R` is its chart over `L`
  with entries mapped into `R`.

## The involution

* `blockInvolutionMatrix e σ` (written `S̃`) and `blockInvolutionMatrixInv e σ` are the
  block-diagonal matrices with blocks `S` and `S⁻¹`, where `S = involutionMatrix e σ`.
  `blockInvolutionMatrix_mul_inv` and `blockInvolutionMatrix_inv_mul` show they are inverse.
  `transpose_blockInvolutionMatrix`: `S̃ᵀ = S̃` when `σ.symmetricSubspace` has dimension
  `|ι| (|ι| + 1) / 2` (from `involutionMatrix_transpose`).
* `matrixChartR_baseChange`: `Φ(τ_R x) = S̃ Φ(x)ᵀ S̃⁻¹` for `Φ = matrixChartR e R` and the
  conjugate transpose `τ = σ.matrix n`. This follows blockwise from the Library's
  `FirstKindInvolution.coefficientEquiv_baseChange` (`(τ_R x)_{ij} = σ_R (x_{ji})`) and
  `chartR_baseChange`. `matrixChartL_baseChange` is the case `R = L`.

## The reduced norm

* `matrixChartL e : L ⊗[K] M_n(D) ≃ₐ[L] M_{n × ι}(L)` is `matrixChartR e L` as an
  `L`-algebra isomorphism (`matrixChartL_apply`). `splittingMap_matrixChartL`: its extension
  to `R` (the Library's `ReducedNorm.splittingMap`) is `matrixChartR e R`.
* `reducedNorm_eq_det_matrixChartR`: for a division algebra `D` that is central and
  finite-dimensional over `K`, and nonempty `n`,
  `CentralSimple.reducedNorm K (M_n(D)) R x = det (matrixChartR e R x)`. This is the Library's
  `CentralSimple.reducedNorm_eq_det_fintype`, which holds for any finite matrix chart.

## The alternating Gram matrix

From here on `D` is a division ring.

* `splitGram e σ H = Φ(1 ⊗ H) S̃` (written `C`) is the split Gram matrix over `L`.
* `exists_splitGram_eq_sub`: if `σ.symmetricSubspace` has dimension `|ι| (|ι| + 1) / 2` and
  `H` is trace-valued antihermitian (`σ.IsAntihermitian H`), then `C = W - Wᵀ`. By the
  Library's `FirstKindInvolution.IsAntihermitian.exists_eq_sub`, `H = V - ᵗV^σ`; take
  `W = Φ(1 ⊗ V) S̃`. Indeed `Φ(1 ⊗ H) = Φ(1 ⊗ V) - S̃ Φ(1 ⊗ V)ᵀ S̃⁻¹`, and `S̃ᵀ = S̃`.
  Consequently `transpose_splitGram` (`Cᵀ = -C`) and `splitGram_diag` (zero diagonal) hold in
  every characteristic.
* `det_splitGram_ne_zero`: `det C ≠ 0` when `H` is a unit.
* `mul_mul_baseChange_eq_iff`: for `u ∈ R ⊗[K] M_n(D)`,
  `u (1 ⊗ H) τ_R(u) = 1 ⊗ H ↔ g C gᵀ = C` with `g = Φ u` and `C` mapped into `R`. Apply the
  ring isomorphism `Φ` and the involution formula. Then multiply on the right by `S̃` or by
  `S̃⁻¹`.

## Provenance

These are standard identifications. Over a splitting field, the antihermitian form becomes an
alternating bilinear form of `|ι|` times the size, and the reduced norm becomes the
determinant. The proofs are direct matrix computations, adapted from the Library's
`Quaternionic.SplittingMatrix` with `Fin 2` replaced by `ι`. They use the Library's
`coefficientEquiv`, `coefficientEquiv_baseChange`, `IsAntihermitian.exists_eq_sub` and
`reducedNorm_eq_det_fintype`, and Mathlib's `Matrix.comp`.
