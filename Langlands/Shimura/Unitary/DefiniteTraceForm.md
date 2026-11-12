# The trace form of an involution and its Gram matrices

Author: Worker 19.

For an involution `τ` of an algebra `B` over a commutative ring `R`, this
module defines the symmetrized trace form

`T(y, z) = tr(L_{τ(y) z}) + tr(L_{τ(z) y})`,

where `L_a` is left multiplication by `a` and `tr` is the regular trace. It
then records the linear algebra of `T` in a basis that is needed to show that
`GJ(ℚ)\GJ(𝔸_f)/K` is finite for a definite unitary similitude group `GJ`:

- similitudes `τ(x) x = c` scale `T` by `c`, so their left-multiplication
  matrices `X` satisfy `Xᵀ G X = c G` for the Gram matrix `G`;
- a matrix commuting with all right multiplications is a left
  multiplication;
- for a rational involution `σ` whose real scalar extension is positive, `T`
  is positive definite, every rational quadratic form is bounded by an
  integer multiple of it, and `Γᵀ G Γ = t G` for the matrix `Γ` of left
  multiplication by `γ` forces `σ(γ) γ = t`.

## Provenance

Harris (1999), Section 1, printed p. 301, assumes `J_∞ = ∏ U(n)`: the
unitary group is compact at every real place. Section 3, printed pp.
306–308, uses that for such a definite group the double coset space
`GJ(ℚ)\GJ(𝔸_f)/K` is finite (the list (3.9)). The published predicate
`AlgebraInvolution.IsPositive` (Worker 57, `Positivity`) is the algebraic
form of this compactness, `tr(L_{τ(x) x}) > 0` for `x ≠ 0` (Milne,
*Introduction to Shimura varieties*, Proposition 8.10(c), Definition 8.11).
Positivity for Harris's definite group is the published
`SecondKindInvolution.isPositive_of_hasDefiniteSignature`.

This module is derived: the trace form, its Gram matrix identities and the
recognition argument were written for this module as steps of the standard
reduction-theory proof of finiteness. None of it is taken from Harris.

The form is symmetrized on purpose. The unsymmetrized form
`tr(L_{τ(y) z})` is in general not symmetric: since `τ` reverses products,
`tr(L_{τ(a)}) = tr(R_a)`, so its values at `(1, a)` and `(a, 1)` are
`tr(L_a)` and `tr(R_a)`. These differ for non-semisimple algebras: upper
triangular `2 × 2` matrices with the involution `x ↦ J xᵀ J`
(`J` antidiagonal) have `tr(L_{e₁₁}) = 2` and `tr(R_{e₁₁}) = 1`. For a positive involution
`T(y, y) = 2 tr(L_{τ(y) y})`.

## Setting

- `AlgebraInvolution R B` (published, `Involution`): an `R`-linear
  anti-automorphism `τ` of `B` of order two. `τ.baseChange S` is its
  extension to `S ⊗_R B` (published).
- `Langlands.Algebra.regularTrace R B a = tr(L_a)` and
  `Langlands.Algebra.regularTraceForm` (published, `RegularTrace`), and
  `Langlands.Algebra.regularTrace_one_tmul`: the regular trace commutes with
  scalar extension (published, `RationalTrace`).
- `σ.Points S` (published, `Adelic`) is the similitude group of
  `σ.baseChange S`: pairs of units `(g, c)` of `S ⊗_R B` and `S` with
  `g σ(g) = c` (`mem_similitudes_iff`, published, `Similitude`).
- `Algebra.leftMulMatrix b x` (Mathlib) is the matrix of `L_x` in the basis
  `b`, and `LinearMap.BilinForm.toMatrix b` the Gram matrix in `b`.

## Declarations

### General rings

- `traceForm τ` (definition): the bilinear form `T` above
  (`traceForm_apply`). It is symmetric (`traceForm_comm`,
  `traceForm_isSymm`).
- `traceForm_mul_mul`: if `τ(x) x = c` with `c ∈ R`, then
  `T(x y, x z) = c T(y, z)`. Indeed `τ(x y) (x z) = τ(y) τ(x) x z = c τ(y) z`,
  and similarly with `y, z` exchanged.
- `apply_mul_self_of_mul_apply`: for a unit `x`, `x τ(x) = c` implies
  `τ(x) x = c`. From `τ(x) = x⁻¹ c` and centrality of `c`.
- `leftMulMatrix_transpose_mul_toMatrix_traceForm`: if `τ(x) x = c`, then
  `Xᵀ G X = c G` for `X` the matrix of `L_x` and `G` the Gram matrix of `T`
  in a basis `b`. This is `traceForm_mul_mul` in matrix form.
- `rightMulMatrix b y` (definition): the matrix of right multiplication `R_y`
  in the basis `b` (`rightMulMatrix_apply`: entry `(i, j)` is the `i`-th
  coordinate of `b_j y`).
- `leftMulMatrix_mul_rightMulMatrix`: left and right multiplication matrices
  commute, by associativity.
- `exists_leftMulMatrix_eq`: a matrix `M` commuting with the right
  multiplication matrices of all basis vectors `b_k` is the left
  multiplication matrix of some `γ`. Let `Γ` be the linear map of `M`. Then
  `Γ(z b_k) = Γ(z) b_k` for all `k`, hence `Γ(z a) = Γ(z) a` for all `a` by
  linearity, and `Γ(a) = Γ(1) a`. Take `γ = Γ(1)`.

### Scalar extension

For `B` free and finite over `R` and a commutative `R`-algebra `S`, with the
scalar-extended basis `Algebra.TensorProduct.basis S b` of `S ⊗_R B`:

- `traceForm_baseChange_tmul`: the trace form of `σ.baseChange S` on
  `1 ⊗ y, 1 ⊗ z` is the image of `T(y, z)` in `S`, by
  `regularTrace_one_tmul`.
- `toMatrix_traceForm_baseChange`: hence the Gram matrix of the extended
  trace form in the extended basis is the image of the rational Gram matrix.
- `leftMulMatrix_one_tmul`, `rightMulMatrix_one_tmul`: the left and right
  multiplication matrices of `1 ⊗ y` are the images of those of `y`.
- `points_leftMulMatrix_transpose_mul_gram`: for a point `(g, c)` of
  `σ.Points S`, the matrix `X` of `L_g` in the extended basis satisfies
  `Xᵀ G X = c G`, with `G` the Gram matrix of `T` in `b` mapped to `S`. This
  combines `apply_mul_self_of_mul_apply`,
  `leftMulMatrix_transpose_mul_toMatrix_traceForm` and
  `toMatrix_traceForm_baseChange`.

### Real quadratic forms

- `exists_dotProduct_mulVec_le`: if the real matrix `G` satisfies
  `vᵀ G v > 0` for all `v ≠ 0`, then for every real matrix `H` there is a
  constant `C` with `vᵀ H v ≤ C vᵀ G v` for all `v`. The quadratic form of
  `G` attains a positive minimum `m` on the unit sphere of the sup norm, so
  `vᵀ G v ≥ m ‖v‖²`, while `vᵀ H v ≤ (∑ |H_{ij}|) ‖v‖²`. Take
  `C = (∑ |H_{ij}|) / m`.

### Positive involutions

- `traceForm_self_pos_of_isPositive`: for a positive involution `τ` of a
  real algebra (published `IsPositive`), `T(y, y) > 0` for `y ≠ 0`, since
  `T(y, y) = 2 tr(L_{τ(y) y})`.

For the remaining results `A` is a finite-dimensional `ℚ`-algebra and `σ` an
involution of `A` with `(σ.baseChange ℝ).IsPositive`.

- `traceForm_self_pos`: `T(a, a) > 0` for `a ≠ 0`. The element `1 ⊗ a` of
  `ℝ ⊗_ℚ A` is nonzero, and its trace form value is the image of `T(a, a)`
  (`traceForm_baseChange_tmul`).
- `dotProduct_toMatrix_traceForm_mulVec_pos`: in a basis `b`, the Gram
  matrix `G` of `T` satisfies `vᵀ G v > 0` for every nonzero rational vector
  `v`.
- `exists_dotProduct_mulVec_le_traceForm`: for every rational matrix `H`
  there is a natural number `C` with `vᵀ H v ≤ C vᵀ G v` for all rational
  `v`. Apply `exists_dotProduct_mulVec_le` to the images of `G` and `H` in
  real matrices; the real Gram matrix is positive definite by
  `traceForm_self_pos_of_isPositive` in the extended basis. Round the
  constant up to a natural number.
- `apply_mul_self_eq_of_traceForm` (recognizing similitudes): if
  `T(γ y, γ z) = t T(y, z)` for all `y, z` and some `t ∈ ℚ`, then
  `σ(γ) γ = t`. Put `w = σ(γ) γ - t`; then `σ(w) = w` and
  `σ(γ y)(γ z) - t σ(y) z = σ(y) w z`. Taking `y = 1, z = w` in the
  hypothesis gives `tr(L_{w w}) + tr(L_{σ(w) w}) = 0`, that is
  `T(w, w) = 0`, so `w = 0` by `traceForm_self_pos`.
- `apply_mul_self_eq_of_gram`: the matrix form, `Γᵀ G Γ = t G` for the
  matrix `Γ` of `L_γ` implies `σ(γ) γ = t`.

## Qualifications

- This module provides tools only; the finiteness of
  `GJ(ℚ)\GJ(𝔸_f)/K` itself is not proved here.
- The positivity results assume `(σ.baseChange ℝ).IsPositive` for the
  involution over `ℚ`; deriving it for Harris's group is the published
  `isPositive_of_hasDefiniteSignature`.
