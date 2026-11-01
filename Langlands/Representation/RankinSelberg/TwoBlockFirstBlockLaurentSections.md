# First-block coefficient functions of a two-block section

Author: Worker 1037.

This is derived internal material for JPSS (1983), Section 4.9, printed pages
416–418. The original first block is evaluated along `diag(v, 1)`. The module
uses the published lower induced sections `TwoBlockJacquet.Sections` and the scalar
section `scalarSection ell f g a = (⊗ ℓ_i)((σ_0 ⊗ σ_1)(a) f(g))`.

## Contraction and coefficient function

`secondContraction ℓ_1` is the linear map `⊗_i W_i → W_0` induced by
`w ↦ ℓ_1(w_1) w_0`. `tensorContraction_blockTensor_blockPair_one` proves that the
contraction against `ℓ_0 ⊗ ℓ_1`, after acting by the Levi element `diag(v, 1)`,
equals `ℓ_0(σ_0(v) y)`. Here `y` is the contraction of the second factor. The proof
is induction on the tensor product.

`firstBlockCoefficient ell f g` is the actual element `modelMap (σ 0) (ell 0) y` of
the coefficient image of `σ_0`, for `y = (1 ⊗ ℓ_1) f(g)`.
`firstBlockCoefficient_apply` shows that its value at `v` is
`scalarSection ell f g (diag(v, 1))`.

## Covariance

`scalarSection_lowerRadical_mul` uses the published covariance `scalarSection_covariant`.
The lower radical `R(Z)` lies in the lower parabolic with trivial Levi projection, so
it leaves every scalar section unchanged. Consequently
`firstBlockCoefficient_lowerRadical_mul` shows that `R(Z) g` and `g` have the same
coefficient function.

`scalarSection_firstBlockEmbedding_mul` applies the same covariance with
`q = diag(v, 1)`. The scalar section at `diag(v, 1) g` and Levi identity equals the
inverse of the actual upper-block half modulus of `diag(v, 1)` times the
coefficient function at `v`.

## Half modulus

`inv_leviHalfModulus_blockPair_one` evaluates the published Levi modulus
`|det b_0|^(m_1+1) / |det b_1|^(m_0+1)` at `(v, 1)`. It identifies the inverse half
modulus with the published determinant weight `|det v|^(-(m_1+1)/2)` for the
normalized absolute value.
