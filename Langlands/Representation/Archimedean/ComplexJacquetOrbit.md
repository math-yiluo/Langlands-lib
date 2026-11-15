# Smoothness of matrix coefficients on skew-Hermitian matrices

Module: `Langlands.Representation.Archimedean.ComplexJacquetOrbit`.

## Purpose and provenance

This is the second helper module for `Langlands.Archimedean.complexJacquetFrobenius` (see
`ComplexJacquetFrobeniusProof.md`). The Library definition `IsComplexGKModule n ρ π` only asks
that `U(n)` acts locally finitely, that matrix coefficients are continuous, that curves through `1`
differentiate to `π`, and that `π` is `U(n)`-equivariant. It does not state that matrix
coefficients are smooth functions on `U(n)`. To build smooth functions on `GL_n(ℂ)` from `ρ`, this
module proves the following. For `w ∈ V` and a linear form `μ`, there is a `C^∞` function `G` on
all complex `n × n` matrices (as a real vector space) such that `G(Y) = μ(ρ(exp Y) w)` for every
skew-Hermitian `Y`.

This is the standard fact that a finite-dimensional continuous representation of a Lie group is
smooth and is the exponential of its differential. The module makes no literature claim beyond
this. `OrbitFrame`, `orbitMatrix` and `orbitLie` are auxiliary devices of this formalization.

## Proof route

Since `w` is `U(n)`-finite (first clause of `IsComplexGKModule`), its orbit span
`W = span{ρ(k) w}` is finite-dimensional. Choose a basis `e_1, …, e_d` of `W` and extend the
coordinate functionals to linear forms `λ_i` on `V` (an `OrbitFrame`). The matrices
`M(k)_ij = λ_i(ρ(k) e_j)` satisfy `M(1) = 1` and `M(kk') = M(k) M(k')` because `W` is
`ρ`-stable. Moreover `μ(ρ(k) w) = ∑ᵢⱼ λ_j(w) μ(e_i) M(k)_ij`.

Fix a skew-Hermitian `Y`. The curve clause of `IsComplexGKModule`, applied to `t ↦ exp(tY)` and
the vectors `e_j`, gives `M'(0) = A(Y)` with `A(Y)_ij = λ_i(π(1 ⊗ Y) e_j)`. The group law gives
`M(exp(tY)) = M(exp(sY)) M(exp((t − s)Y))`, so `M'(s) = M(s) A(Y)` for every `s`, and the matrix
ODE `M' = MA`, `M(0) = 1` forces `M(exp(tY)) = exp(t A(Y))`. Since `Y ↦ A(Y)` is defined and
real-linear on all matrices, `G(Y) = ∑ᵢⱼ λ_j(w) μ(e_i) exp(A(Y))_ij` is `C^∞` and agrees with
`μ(ρ(exp Y) w)` on skew-Hermitian `Y`.

## Declarations

All declarations are in the namespace `Langlands.Archimedean`.

- `contDiff_matrix_exp m`: the matrix exponential on `m × m` complex matrices is `C^∞` over `ℝ`
  (it is analytic).
- `eq_exp_of_hasDerivAt_mul`: if `M : ℝ → M_m(ℂ)` satisfies `M'(t) = M(t) A` for all `t` and
  `M(0) = 1`, then `M(t) = exp(tA)`. The proof shows that `M(t) exp(−tA)` has derivative zero.
- `OrbitFrame ρ w` (structure): a natural number `dim`, vectors `vec j` in the orbit span
  `FiniteVectors.orbitSpan ρ w`, and linear forms `coord i` on `V` with
  `coord i (vec j) = δ_ij` and `∑ᵢ coord i x • vec i = x` for every `x` in the orbit span.
- `exists_orbitFrame`: a `U(n)`-finite vector has an orbit frame.
- `orbitMatrix fr k` (definition): the matrix `(coord i (ρ k (vec j)))_ij`; `orbitMatrix_apply`
  unfolds it.
- `OrbitFrame.rho_vec_mem`, `OrbitFrame.rho_vec`: `ρ(k) e_j` lies in the orbit span and equals
  `∑ᵢ M(k)_ij e_i`.
- `orbitMatrix_one`, `orbitMatrix_mul`: `M(1) = 1` and `M(kk') = M(k) M(k')`.
- `OrbitFrame.apply_rho`: `μ(ρ(k) w) = ∑ᵢ ∑ⱼ λ_j(w) μ(e_i) M(k)_ij`.
- `orbitLie π fr` (definition): the real-linear map `Y ↦ (λ_i(π(1 ⊗ Y) e_j))_ij` on all
  matrices; `orbitLie_apply` unfolds it.
- `orbitMatrix_skewExp`: for `IsComplexGKModule n ρ π` and skew-Hermitian `Y`,
  `M(exp(tY)) = exp(t A(Y))` for every real `t`.
- `IsComplexGKModule.exists_contDiff_coeff`: for `IsComplexGKModule n ρ π`, `w ∈ V` and a
  linear form `μ`, there is `G` with `ContDiff ℝ ∞ G` and `G Y = μ(ρ(skewExp Y hY) w)` for every
  skew-Hermitian `Y`.
