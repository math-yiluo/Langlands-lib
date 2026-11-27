# Traces under restriction of scalars

Module `Langlands.Algebra.RestrictScalarsTrace`, namespace
`Langlands.Algebra.RestrictScalarsTrace`. It uses only Mathlib.

## Declarations

- `trace_restrictScalars`: let `A` be a commutative `R`-algebra that is finite free as an
  `R`-module, and `M` a finite free `A`-module with a compatible `R`-module structure
  (`IsScalarTower R A M`). For an `A`-linear endomorphism `f` of `M`,

  ```text
  tr_R (f viewed as R-linear) = Tr_{A/R} (tr_A f),
  ```

  where `Tr_{A/R} = Algebra.trace R A`. Proof: take bases `b_A` of `A` over `R` and `b_M` of
  `M` over `A`. In the product basis `b_A.smulTower' b_M`, Mathlib's
  `LinearMap.restrictScalars_toMatrix` gives the matrix of `f` over `R` as the block matrix
  whose `(i, j)` block is the left-multiplication matrix of the `(i, j)` entry of the matrix of
  `f` over `A`. The trace of this block matrix is the sum over `i` of the traces of the diagonal
  blocks. That sum is `Σ_i Tr_{A/R}(f_{ii}) = Tr_{A/R}(tr_A f)` (`Algebra.trace_eq_matrix_trace`).
- `algebraTrace_pi`: for finitely many finite free `R`-algebras `S_i`,
  `Tr_{(Π_i S_i)/R}(x) = Σ_i Tr_{S_i/R}(x_i)`. Proof: compute in the basis `Pi.basis` of the
  product; the diagonal entry at `(i, k)` of left multiplication by `x` is the diagonal entry
  at `k` of left multiplication by `x_i` in `S_i`.
- `algebraTrace_of_I_eq_zero` and `algebraTrace_of_I_ne_zero`: on an `RCLike` field `K`, the
  real trace `Tr_{K/ℝ}(z)` is `Re z` if `I = 0`, and `2 Re z` if `I ≠ 0`. Proof: compute in
  the real basis `{1}` (if `I = 0`) or `{1, I}` (if `I ≠ 0`; then `Im I = 1`), built with
  `Basis.ofEquivFun` from `z ↦ Re z` and `z ↦ (Re z, Im z)`.

## Provenance

Internal. These are standard facts of linear algebra: transitivity of traces in a tower of
free extensions, additivity over products, and the trace of `ℂ` (or `ℝ`) over `ℝ`. Mathlib's
`Algebra.trace_trace` is the corresponding tower formula for algebra traces; the first
theorem here is its form for endomorphisms of a module, with the same block-matrix proof.
