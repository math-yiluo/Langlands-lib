# The grading defined by a bialgebra map to a group algebra

Worker 1395 wrote this module. Let `K` be a commutative ring, `N` a commutative
group, `A` a commutative `K`-bialgebra and `π : A →ₐc[K] K[N]` a bialgebra map.
Geometrically, `π` is a homomorphism from the diagonalizable group `D(N)` to
`Spec A`. Then `A` becomes a right comodule algebra over `K[N]` through
`a ↦ ∑ a₁ ⊗ π a₂`, which is an `N`-grading of `A`. The module develops this
grading with Mathlib's `Coalgebra.Repr` sums. It is an internal helper for the
proof of
[`CentralTorusExtensionStatement`](../GroupScheme/Torus/CentralExtensionProof.md).

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Remark 12.13, printed p.235 (one-based PDF p.251), states the underlying
correspondence for finite-dimensional spaces: "To give a representation of
D(M) on V is the same as giving an M-gradation of V". This module proves only
the facts listed below, by direct Hopf-algebra computation.

## Contents

### Actions of linear forms on a coalgebra

* `ract f`, `lact f`: the right and left actions `a ↦ ∑ f(a₂) a₁` and
  `a ↦ ∑ f(a₁) a₂` of a linear form `f : A →ₗ[K] K`. `conv f g` is the
  convolution `a ↦ ∑ f(a₁) g(a₂)`.
* `ract_apply`, `lact_apply`, `conv_apply` evaluate them on a
  `Coalgebra.Repr` of `a`.
* `ract_ract`: `ract f ∘ ract g = ract (conv f g)`, by coassociativity
  (`Coalgebra.sum_tmul_tmul_eq`).
* `lTensor_ract_comul`, `rTensor_lact_comul`: `ract f` commutes with
  comultiplication on the right tensor factor, and `lact f` on the left one.
* `counit_ract`: `ε (ract f a) = f a`; `ract_counit`: `ract ε = id`.

### Coefficients in the group algebra

* `lcoeff n`: the `n`-th coefficient of `K[N]` as a linear form.
  `conv_lcoeff` shows that these forms are orthogonal idempotents for
  convolution: `conv (lcoeff m) (lcoeff n)` is `lcoeff n` if `m = n` and `0`
  otherwise.
* `counit_eq_sum`: the counit of `K[N]` is the sum of the coefficients.
* `coeff_scalarTensorEquiv`, `sum_scalarTensorEquiv`: under Mathlib's
  `AddMonoidAlgebra.scalarTensorEquiv : A ⊗ K[N] ≃ A[N]`, the `n`-th
  coefficient is `(id ⊗ lcoeff n)` and the sum of coefficients is `(id ⊗ ε)`.

### The grading

* `coeffForm π n`: the form `a ↦ (π a)ₙ`. `proj π n := ract (coeffForm π n)`
  is the projection to degree `n`, `a ↦ ∑ (π a₂)ₙ a₁`.
* `conv_coeffForm`, `proj_proj`: the projections are orthogonal idempotents.
  `counit_proj`: `ε (proj π n a) = (π a)ₙ`. `lTensor_proj_comul`: `proj π n`
  commutes with comultiplication on the right factor.
* `coaction π : A →ₐ[K] A[N]`: the algebra map
  `scalarTensorEquiv ∘ (id ⊗ π) ∘ Δ`. `coeff_coaction` identifies its
  `n`-th coefficient with `proj π n`, and `sum_coeff_coaction`, `sum_proj`
  show that `a` is the sum of its homogeneous components.
* `grade π n`: the submodule of `a` with `coaction π a = single n a`
  (`mem_grade_iff`). `proj_of_mem`, `proj_self_of_mem` and `proj_mem` say that
  `proj π n` is a projection onto `grade π n`. `one_mem_grade_zero` and
  `mul_mem_grade` say that the grading is multiplicative, and
  `proj_mul_of_mem` computes `proj π n (a * b) = proj π (n - j) a * b` for `b`
  of degree `j`.
* `comul_of_mem`: for `a` of degree `n`, `Δ a = (id ⊗ proj π n) (Δ a)`.
* `inv_mem_grade`: the inverse of a unit of degree `n` has degree `-n`. The
  image of `u⁻¹` under the algebra map `coaction π` is inverse to
  `single n u`, hence equal to `single (-n) u⁻¹`.

### Central gradings

* `IsCentral π`: the left and right coactions agree,
  `(π ⊗ id) (Δ a) = comm ((id ⊗ π) (Δ a))` for all `a`. Geometrically the
  homomorphism `D(N) → Spec A` lands in the centre.
* `IsCentral.lact_coeffForm`: for central `π`, `lact (coeffForm π n) = proj π n`.
  `IsCentral.rTensor_proj_comul` follows from `rTensor_lact_comul`.
* `IsCentral.comul_of_mem`: for central `π` and `a` of degree `n`,
  `Δ a = (proj π n ⊗ proj π n) (Δ a)`. So the comultiplication maps the
  component of degree `n` into the tensor square of that component.

### Strong grading from the antipode

* `one_mem_grade_neg_mul_grade`: if `A` is a Hopf algebra and `a` has degree
  `n` with `ε a = 1`, then `1 ∈ grade π (-n) * grade π n`. Apply the linear map
  `t ↦ proj π 0 (μ ((S ⊗ proj π n) t))` to `Δ a`. On a pure tensor `x ⊗ y`,
  `proj_mul_of_mem` turns the value into `proj π (-n) (S x) * proj π n y`,
  which lies in the product. By `comul_of_mem`, the value at `Δ a` is
  `proj π 0 (∑ S a₁ a₂) = proj π 0 (ε a • 1) = 1`.
