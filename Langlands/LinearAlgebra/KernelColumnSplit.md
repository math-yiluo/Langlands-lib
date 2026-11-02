# Kernels of matrices with a split block of columns

Author: Worker 766.

This module is in the namespace `Langlands.LinearAlgebra.KernelColumnSplit`. It is
plain linear algebra over commutative rings. It imports only Mathlib and the
Library lemma
`Langlands.Cohomology.ModuleComplex.FibreH0Spread.exists_mul_eq_smul_one`
(module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Split`).

## Purpose and provenance

This is an internal helper for the diagonal branch of the proof of
`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafAlgebraicSpaceStatement`. There
the global sections of a line bundle on `X ×_k Spec A` are computed as the kernel
of `d ⊗ A` for a fixed map `d : M₀ → M₁` of finite free modules over a base ring
`R`. The module studies this kernel locally on `Spec R`. Near a point `p`, choose
a maximal block of columns of the matrix of `d` that stays linearly independent
at `p`, and a left inverse of the block up to a scalar `t` that is nonzero at
`p`. Over any `R`-algebra `A` in which `t` is invertible, the kernel of `d ⊗ A`
is the kernel of the Schur complement of the block. If moreover the Schur
complement vanishes over `A`, this kernel is free on the remaining columns. If an
element `u` of `R` that is a unit in `A` kills the Schur complement over `R`, then
the kernel of `d ⊗ A` is spanned by finitely many explicit vectors of the kernel
of `d` over `R`.

No literature theorem is claimed. The ingredients are standard:

- McCoy's theorem in matrix form: a square matrix with linearly independent
  columns has a determinant that is a non-zero-divisor. Mathlib provides it as
  `Matrix.Nonsingular.of_linearIndependent_col` together with
  `Matrix.nonsingular_iff_det_mem_nonZeroDivisors`.
- The Schur complement of a block of columns, and elimination of the
  coordinates of that block.

## McCoy for kernels

`eq_zero_of_ker_linearEquiv` concerns a matrix `S : Matrix m n A` over a
commutative ring `A`, with `n` finite and `m` arbitrary. If the kernel of
`S.mulVecLin` is linearly equivalent to `n → A`, then `S = 0`.

The proof composes the inverse equivalence with the inclusion of the kernel. This
gives an injective linear map `φ : (n → A) → (n → A)` whose image lies in the
kernel of `S`. Let `Φ` be its matrix. Its columns are linearly independent, so by
McCoy `det Φ` is a non-zero-divisor. From `S * Φ = 0` one gets
`det Φ • S = S * Φ * adjugate Φ = 0`, hence `S = 0`.

## Column blocks and the Schur complement

Here `P : Matrix m κ A`, `Q : Matrix m α A`, `G : Matrix κ m A` and `c : A`, with
`m`, `κ` and `α` finite.

- `schur P Q G c` is the matrix `c • Q - P * (G * Q)`. `schur_map` states that it
  commutes with applying a ring homomorphism entrywise.
- Assume `G * P = c • 1`, and let `v` be a vector indexed by `κ ⊕ α` with
  `fromCols P Q *ᵥ v = 0`. Write `v_κ` and `v_α` for its two blocks. Then
  `schur_mulVec_eq_zero_of_mulVec_eq_zero` gives `schur P Q G c *ᵥ v_α = 0`, and
  `mulVec_eq_neg_of_mulVec_eq_zero` gives `(G * Q) *ᵥ v_α = -(c • v_κ)`.
- Now let `c` be a unit. `kerLift Q G hc y` is the vector with blocks
  `-c⁻¹ • ((G * Q) *ᵥ y)` and `y`. `fromCols_mulVec_kerLift` computes
  `fromCols P Q *ᵥ kerLift Q G hc y = c⁻¹ • (schur P Q G c *ᵥ y)`; this needs no
  hypothesis on `G`.
- `kerFromColsEquiv` assumes that `c` is a unit and `G * P = c • 1`. It is an
  `A`-linear equivalence from the kernel of `fromCols P Q` to the kernel of
  `schur P Q G c`. It sends `v` to `v_α`, and its inverse is `kerLift`.

## Kernels and matrices

`kerEquivMatrix b₀ b₁ f` assumes that `b₀` and `b₁` are finite bases of `M₀` and
`M₁`. It identifies the kernel of `f : M₀ → M₁` with the kernel of the matrix
`LinearMap.toMatrix b₀ b₁ f`, by sending a vector to its coordinates in `b₀`
(`kerEquivMatrix_apply`).

## Column splits

Let `R` be a commutative ring and `d : M₀ →ₗ[R] M₁` a linear map. The structure
`ColumnSplit d` packages the following data.

- Index types `κ`, `α` and `ι` in `Type`. They are finite, and `κ` and `α` have
  decidable equality.
- A basis `b₀` of `M₀` indexed by `κ ⊕ α`, and a basis `b₁` of `M₁` indexed by `ι`.
- A scalar `t : R` and a matrix `inv : Matrix κ ι R` with
  `inv * P = t • 1`. Here `P` is the block of columns of
  `LinearMap.toMatrix b₀ b₁ d` indexed by `κ`.

For a split `S`:

- `S.P` and `S.Q` are the blocks of columns indexed by `κ` and `α`.
  `S.schurMatrix` is `schur S.P S.Q S.inv S.t`, a matrix with rows `ι` and
  columns `α`. `inv_mul_P` restates the field `inv_mul` in terms of `S.P`.
- Let `A` be an `R`-algebra. `toMatrix_baseChange_eq` states that the matrix of
  `d.baseChange A` in the base-changed bases is
  `fromCols (S.P.map (algebraMap R A)) (S.Q.map (algebraMap R A))`.
  `inv_mul_P_map` is the identity `inv * P = t • 1` mapped to `A`.
- `kerBaseChangeEquiv ht` assumes that the image of `t` in `A` is a unit. It is an
  `A`-linear equivalence from the kernel of `d.baseChange A` to the kernel of the
  image of `S.schurMatrix` over `A`. It sends `w` to its coordinates in the
  base-changed basis at the indices `Sum.inr j`, for `j : α`
  (`kerBaseChangeEquiv_apply`).
- `schurMatrix_map_eq_zero` assumes that the image of `t` in `A` is a unit and that
  the kernel of `d.baseChange A` is linearly equivalent to `α → A`, with any
  equivalence. Then the image of `S.schurMatrix` in `A` is zero. This is the McCoy
  lemma above applied to the Schur complement.
- Conversely, `kerBaseChangeEquivFun ht h0` assumes that the image of `t` is a unit
  and the image of the Schur complement is zero. It identifies the kernel of
  `d.baseChange A` with `α → A` by the same coordinates
  (`kerBaseChangeEquivFun_apply`).

### Explicit kernel vectors

- `fromCols_mulVec_kerCoords` is an identity over `R`. The vector with blocks
  `-((inv * Q) *ᵥ y)` and `t • y` is sent by `fromCols P Q` to
  `S.schurMatrix *ᵥ y`.
- `kerVector u j` is the vector of `M₀` whose coordinates in `b₀` are `u` times
  the blocks `-((inv * Q) *ᵥ e_j)` and `t • e_j`. Here `e_j` is the standard basis
  vector of `α → R` (`repr_kerVector`).
- `kerVector_mem_ker`: if `u • S.schurMatrix = 0`, then every `kerVector u j` lies
  in the kernel of `d`.
- `exists_eq_sum_kerVector` assumes that `u • S.schurMatrix = 0` and that the
  images of `t` and `u` in the `R`-algebra `A` are units. Then every element `w` of
  the kernel of `d.baseChange A` is a sum `∑ j, a j • (1 ⊗ kerVector u j)` with
  coefficients `a j` in `A`. The proof compares coordinates at the indices
  `Sum.inr j`. The vector `1 ⊗ kerVector u j` has coordinate `u t` at `Sum.inr j`
  and `0` at the other indices `Sum.inr j'`. Coordinates at these indices determine
  an element of the kernel, by `kerBaseChangeEquivFun`. So
  `a j = (u t)⁻¹ · w_j` works.
- `kerBaseChange_le_range` is the consequence that, under the same hypotheses, the
  kernel of `d.baseChange A` is contained in the image of `A ⊗ ker d` under the
  base change of the inclusion `ker d → M₀`.
- `exists_pow_smul_schurMatrix_eq_zero` assumes that `Rᵤ` is a localization of `R`
  away from `u` and that the image of `S.schurMatrix` in `Rᵤ` is zero. Then
  `u ^ n • S.schurMatrix = 0` for some `n`.

Combining the last two results: suppose that `t` is invertible in `R[1/u]` and
the Schur complement vanishes over `R[1/u]`. Take `n` from
`exists_pow_smul_schurMatrix_eq_zero`. For every `R`-algebra `A` in which `u` is a
unit, the images of `t` and `u ^ n` in `A` are units. So by
`exists_eq_sum_kerVector` the vectors `1 ⊗ kerVector (u ^ n) j` span the kernel of
`d ⊗ A`. This combination is not stated as a separate Lean theorem.

## Splits at field points

`exists_columnSplit` assumes that `M₀` and `M₁` are finite free `R`-modules and
that `K` is a field with an `R`-algebra structure. For every `d`, there is a
column split `S` of `d` such that:

- the image of `S.t` in `K` is nonzero, and
- the number of remaining columns, `Fintype.card S.α`, equals
  `Module.finrank K` of the kernel of `d.baseChange K`.

The proof uses the bases `Module.finBasis` and the image `D` of the matrix of `d`
in `K`. Mathlib's `exists_linearIndependent'` chooses a family of columns of `D`
that is linearly independent and spans the column space. These columns form the
block `κ`, and the other columns form `α`. Their images in `K` are linearly
independent. So the Library lemma `exists_mul_eq_smul_one` gives a left inverse
of the block up to a scalar `t` that is nonzero in `K`. The proof of that lemma
takes for `t` a maximal minor of the block.
Finally, rank-nullity for `D` gives
`card κ + finrank ker = card κ + card α`.
