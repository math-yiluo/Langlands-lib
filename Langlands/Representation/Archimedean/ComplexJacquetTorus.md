# Jacquet functionals on the diagonal unitary torus

Module: `Langlands.Representation.Archimedean.ComplexJacquetTorus`.

## Purpose and provenance

This module is the first of six helper modules for the proof
`Langlands.Archimedean.complexJacquetFrobenius` of
`Langlands.Archimedean.ComplexJacquetFrobeniusStatement` (Frobenius reciprocity for Jacquet
functionals of `(𝔤𝔩_n(ℂ), U(n))`-modules; see `ComplexJacquetFrobeniusProof.md`). It works with
the Library predicates `IsComplexGKModule n ρ π` (module `GKModule`) and
`IsComplexJacquetFunctional n π ℓ a b` (module `ComplexJacquetReduction`). The latter says that
`ℓ` kills `π(1 ⊗ X) v` for strictly upper triangular `X`, and that the diagonal unit
`E_jj` acts by `a_j` and `i E_jj` acts by `b_j`: `ℓ(π(1 ⊗ E_jj) v) = a_j ℓ(v)` and
`ℓ(π(1 ⊗ i E_jj) v) = b_j ℓ(v)`.

The module proves two facts about a nonzero Jacquet functional `ℓ`:

1. the imaginary exponents are integral, `b_j = i l_j` with `l_j ∈ ℤ`;
2. a diagonal unitary matrix `m` acts on `ℓ` by the character `m ↦ ∏ⱼ m_jj^{l_j}`, that is,
   `ℓ(ρ(m) w) = (∏ⱼ m_jj^{l_j}) ℓ(w)`.

This is the elementary fact that a `(𝔤, K)`-module integrates on the compact torus
`T = U(n) ∩ (diagonal matrices)` and that the characters of `T` are given by integer weights. It
is part of Wallach's construction of the embedding into a principal series (N. Wallach,
*Representations of reductive Lie groups*, Proc. Sympos. Pure Math. 33 (1979), 4.16–4.17), where
the `M ∩ K`-type of the Jacquet module appears. The Lean statements below are internal lemmas;
they make no literature claim beyond these standard facts. The definitions `skewExp` and `diagI`
are auxiliary devices of this formalization.

## Proof route

For a skew-Hermitian matrix `Y` (`star Y = -Y`), `exp(tY)` is unitary and
`t ↦ exp(tY)` is a one-parameter subgroup of `U(n)`. The curve clause of `IsComplexGKModule`
(the third component `hgk.2.2.1`) says that `t ↦ μ(ρ(k(t)) w)` is differentiable at `0` with
derivative `μ(π(1 ⊗ Y) w)` for every curve `k` in `U(n)` with `k(0) = 1` whose entries have
derivatives `Y_ij` at `0`. Combined with the group law `exp((s + t)Y) = exp(sY) exp(tY)` this gives
the derivative at every `s` (`hasDerivAt_skewExp`).

For the diagonal skew-Hermitian matrix `Y = diag(iθ_1, …, iθ_n)`, the matrix `exp(sY)` commutes
with `Y`, so the conjugation clause of `IsComplexGKModule` (`hgk.2.2.2`) turns the derivative of
`φ(t) = ℓ(ρ(exp(tY)) w)` into `ℓ(π(1 ⊗ Y) ρ(exp(sY)) w)`. By the Jacquet clauses this equals
`c φ(s)` with `c = ∑ⱼ θ_j b_j`. The scalar ODE `φ' = cφ` then gives
`φ(1) = exp(c) φ(0)` (`apply_skewExp_diagI`). Taking `θ = 2π e_j` makes `exp(Y) = 1`, so
`exp(2π b_j) = 1` whenever `ℓ(w) ≠ 0`. Hence `2π b_j ∈ 2πi ℤ`, that is, `b_j ∈ iℤ`
(`exists_int`).
Finally every diagonal unitary `m` equals `exp(diag(i arg m_jj))`, which gives the weight formula
(`exists_weight`).

## Declarations

All declarations are in the namespace `Langlands.Archimedean`.

### Exponentials of skew-Hermitian matrices

- `star_real_smul_of_skew`: if `star Y = -Y` then `star (t • Y) = -(t • Y)` for real `t`.
- `skewExp Y hY` (definition): the element `exp Y` of `Matrix.unitaryGroup (Fin n) ℂ` for a
  skew-Hermitian `Y`; `coe_skewExp` says its underlying matrix is `NormedSpace.exp Y`.
- `skewExp_zero_smul`, `skewExp_add_smul`: `exp(0 • Y) = 1` and
  `exp((s + t) • Y) = exp(s • Y) exp(t • Y)`.
- `hasDerivAt_exp_smul_zero`: `t ↦ exp(t • Y)` has derivative `Y` at `0`.
- `hasDerivAt_entry`: entries of a differentiable matrix curve are differentiable, with the
  corresponding entries of the derivative.
- `hasDerivAt_skewExp_entry`: the entries of `t ↦ skewExp (t • Y)` have derivatives `Y i j`
  at `0`.

### Derivatives along one-parameter subgroups

- `hasDerivAt_skewExp`: for `IsComplexGKModule n ρ π`, skew-Hermitian `Y`, any linear form `μ`
  and vector `w`, the function `t ↦ μ(ρ(exp(tY)) w)` has derivative
  `μ(ρ(exp(sY)) π(1 ⊗ Y) w)` at every real `s`.
- The scalar ODE `φ' = c φ` on `ℝ` is solved by the Library lemma
  `Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt` (module
  `Langlands.Automorphic.CuspidalAdmissible.CentralEigen`): if `φ : ℝ → ℂ` satisfies
  `φ'(t) = c φ(t)` for all `t`, then `φ(t) = exp(ct) φ(0)`. This module does not restate it.

### Jacquet functionals on upper triangular directions

- `one_tmul_real_smul`, `lie_one_tmul_real_smul`, `lie_one_tmul_add`, `lie_one_tmul_sum`:
  real-linearity of `M ↦ π(1 ⊗ M) v`.
- `single_eq_re_add_im`: `z E_jj = Re z · E_jj + Im z · (i E_jj)`.
- `IsComplexJacquetFunctional.apply_upper`: for upper triangular `X`,
  `ℓ(π(1 ⊗ X) v) = (∑ⱼ (Re X_jj · a_j + Im X_jj · b_j)) ℓ(v)`. The proof splits `X` into its
  diagonal `D` and the strictly upper triangular `X − D`.

### Upper triangular unitary matrices

- `offDiag_eq_zero_of_upper_unitary`: an upper triangular unitary matrix is diagonal. This is
  the Library theorem `Langlands.GroupScheme.GeneralLinear.mem_blockLeviSubgroup_of_unitary`
  (module `Langlands.GroupScheme.Dynamic.UnitaryLeviIntersection`: a unitary matrix in the block
  parabolic subgroup of an integer weight `e` lies in its block Levi subgroup), specialized to
  `g = m` and the decreasing weights `e i = -i`. For these weights, membership in the block
  parabolic subgroup means `m_ij = 0` whenever `e i < e j`, that is, whenever `j < i`. That is
  upper triangularity. Membership in the block Levi subgroup means `m_ij = 0` whenever
  `e i ≠ e j`, that is, whenever `i ≠ j`.

### The diagonal unitary torus

- `diagI θ` (definition): the diagonal matrix `diag(iθ_1, …, iθ_n)` for `θ : Fin n → ℝ`;
  `star_diagI`: it is skew-Hermitian; `exp_diagI`: `exp(diagI θ) = diag(exp(iθ_j))`.
- `IsComplexJacquetFunctional.apply_skewExp_diagI`: for a Jacquet functional `ℓ` with exponents
  `a`, `b`, `ℓ(ρ(exp(diag(iθ))) w) = exp(∑ⱼ θ_j b_j) ℓ(w)`.
- `IsComplexJacquetFunctional.exists_int`: if `ℓ ≠ 0` there are integers `l_j` with
  `b_j = i l_j` for all `j`.
- `norm_diag_eq_one_of_unitary`: a diagonal unitary matrix has diagonal entries of norm `1`.
- `IsComplexJacquetFunctional.exists_weight`: if `ℓ ≠ 0` there are integers `l_j` with
  `b_j = i l_j`, and `ℓ(ρ(m) w) = (∏ⱼ m_jj^{l_j}) ℓ(w)` for every diagonal unitary `m` and every
  `w`.
