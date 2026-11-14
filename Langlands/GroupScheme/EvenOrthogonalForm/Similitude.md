# The orthogonal adjoint involution and similitudes of the split hyperbolic form

This module collects matrix identities for the split hyperbolic quadratic form
on `l ⊕ l` over a commutative ring `R`. Its Gram matrix is
`Q = formMatrix l R = [[0, 1], [0, 0]]` and its polar matrix is
`J = polarMatrix l R = [[0, 1], [1, 0]]`. A matrix `x` is orthogonal when
`x Q xᵀ - Q` is alternating (`IsAlt M` means `M = U - Uᵀ` for some `U`).

## The adjoint involution and the projection

- `orthogonalInvolution R l` is the involution of the first kind
  `τ₀ x = J xᵀ J` of the matrix algebra. It is adjoint to the polar form,
  since `J² = 1`. `orthogonalInvolution_mul_polar` records
  `τ₀(x) J = J xᵀ`, and `orthogonalInvolution_map` records compatibility
  with ring maps applied entrywise.
- `mem_alternatingSubspace_iff`: `M` lies in the alternating subspace
  `{y - τ₀ y}` of `τ₀` exactly when `M J` is alternating. The forward
  direction is `(y - τ₀ y) J = yJ - (yJ)ᵀ`. The converse takes
  `y = U J` for `M J = U - Uᵀ`.
- `leftProjection R l` is `p = [[1, 0], [0, 0]]`. It satisfies `p J = Q`
  (`leftProjection_mul_polar`) and `p + τ₀ p = 1`
  (`leftProjection_add_orthogonalInvolution`), and entrywise maps preserve it.
- `projection_defect_mul_polar`: `(x p τ₀(x) - p) J = x Q xᵀ - Q`. Combined
  with the previous item, `mem_orthogonalGroup_iff_projection` says that `x`
  is orthogonal exactly when `x p τ₀(x) - p` lies in `{y - τ₀ y}`. This is the
  matrix form of the quadratic pair `(τ₀, [p])` of the split form.

## Similitudes

A similitude with multiplier `μ` is a matrix `g` with `g Q gᵀ - μ Q`
alternating. `similitude_polar` shows `g J gᵀ = μ J`: add the transpose
of the alternating difference. With an inverse `g'` (`g' g = 1`) and an
inverse `μ'` of `μ`, the following lemmas rewrite this as `J gᵀ = μ g' J`,
`g J = μ J g'ᵀ` and `g'ᵀ J = μ' J g`:

- `polar_mul_transpose_of_similitude`
- `mul_polar_of_similitude`
- `transpose_inv_mul_polar_of_similitude`

From these:

- `orthogonalInvolution_conj_of_similitude`: `τ₀(g' x g) = g' τ₀(x) g`.
  Conjugation by a similitude commutes with `τ₀`.
- `conj_leftProjection_sub_mem`: `g' p g - p ∈ {y - τ₀ y}`. Conjugation
  by a similitude moves `p` by an alternating element. The proof writes
  `(g' p g - p) J` as `-(g' (g Q gᵀ - μ Q) g'ᵀ)`, using `p J = Q` and
  `g J = μ J g'ᵀ`. This matrix is alternating.

## Matrices commuting with the unipotent orthogonal matrices

`altBasis i j` is the alternating matrix `E_ij - E_ji`. The lemmas
`single_one_mul_apply`, `mul_single_one_apply`, `altBasis_mul_apply` and
`mul_altBasis_apply` compute the entries of the products with a matrix unit.

- `eq_zero_of_altBasis_mul`: if `(E_ij - E_ji) c = 0` for all `i ≠ j`, then
  `c = 0`. This needs only that every index has a different one.
- `eq_scalar_of_mul_altBasis`: if `a (E_ij - E_ji) = (E_ij - E_ji) d` for all
  `i ≠ j`, and any two indices admit a third index different from both
  (at least three indices), then `a = d = a_{i₀ i₀} · 1`.
- `eq_smul_one_of_commute`: a matrix `h` that commutes with the upper and
  lower unipotent orthogonal matrices `[[1, Y], [0, 1]]` and
  `[[1, 0], [Y, 1]]` for `Y = E_ij - E_ji` (`i ≠ j`) is the scalar matrix
  `h_{i₀ i₀} · 1`. Writing `h = [[a, b], [c, d]]` in blocks, commuting with
  the upper matrix gives `Y c = 0` and `a Y = Y d`, and commuting with the
  lower matrix gives `Y b = 0`. By the two preceding lemmas, `b = c = 0` and
  `a = d` is the scalar `a_{i₀ i₀}`.

No hypothesis on the characteristic of `R` is used anywhere.

## Provenance

Derived. The involution `τ₀` and the pair `(τ₀, [p])` follow the
correspondence between quadratic forms and quadratic pairs of
Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*, §5.B, made explicit
for the split hyperbolic form. The statements about similitudes are the
matrix form of the fact that similitudes act on the quadratic pair (KMRT
§12). The centralizer computation is elementary linear algebra. Each
statement is a direct matrix computation, explained above.
