# Detecting divisibility on tensor products by product functionals

Module `Langlands.GroupScheme.IntegralModel.Smoothening.TensorDensity`. This is a
helper module of the proof of
`Langlands.GroupScheme.IntegralModel.SmootheningStatement`. It contains internal
linear-algebra lemmas.

## Over a field

For a field `k` and `k`-vector spaces `V` and `W`, a family `F` of linear forms
on `V` satisfies `Detects F` when the only vector killed by every form is `0`.

`detects_tensor`: let `F` detect zero on `V` and `G` detect zero on `W`. If
`x ∈ V ⊗ W` is killed by every product form `F i ⊗ G j` (followed by
`k ⊗ k ≅ k`), then `x = 0`. Choose a basis `b` of `V` and write `x` as a finite
sum `∑ b_l ⊗ w_l` (`TensorProduct.equivFinsuppOfBasisLeft`). Then
`(id ⊗ G j) x ∈ V` is killed by every `F i`, hence is zero. Its `l`-th
coordinate is `G j (w_l)`, so each `w_l` is killed by every `G j`, hence is zero.

## Over a local ring

Let `R` be a local ring with maximal ideal `𝔪` and residue field `κ`. Let `C`
and `D` be `R`-modules.

- `one_tmul_eq_zero_iff`: `1 ⊗ c = 0` in `κ ⊗ C` if and only if `c ∈ 𝔪 C`
  (`TensorProduct.quotTensorEquivQuotSMul`). By `exists_one_tmul_eq`, every
  element of `κ ⊗ C` has the form `1 ⊗ c`.
- `reduceForm f : κ ⊗ C →ₗ[κ] κ` is the reduction of an `R`-valued form `f`.
  It satisfies `reduceForm f (1 ⊗ c) = residue (f c)`.
- `DetectsMaximal F`, for a family `F` of `R`-valued forms on `C`, holds when
  every `c` all of whose values `F i c` lie in `𝔪` lies in `𝔪 C`.
  `DetectsMaximal.detects` shows that then the reductions `reduceForm (F i)`
  detect zero on `κ ⊗ C`.
- `productForm f g : C ⊗ D →ₗ[R] R` is `c ⊗ d ↦ f c * g d`
  (`productForm_tmul`). `residue_productForm` identifies its reduction with the
  product of the reductions under `κ ⊗ (C ⊗ D) ≅ (κ ⊗ C) ⊗_κ (κ ⊗ D)`
  (`TensorProduct.AlgebraTensorModule.distribBaseChange`).
- `DetectsMaximal.tensor`: if `F` detects `𝔪` on `C` and `G` on `D`, then the
  product forms detect `𝔪` on `C ⊗ D`. This follows from `detects_tensor` over
  `κ`.

## Over a discrete valuation ring

`DetectsMaximal.exists_eq_smul`: over a discrete valuation ring, let `F` detect
`𝔪` and let `s ≠ 0` divide every value `F i c`. Then `c = s • c'` for some `c'`.
Write `s = u ϖⁿ` (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`) and
induct on `n`. If `ϖ` divides all values of `c`, then `c ∈ 𝔪 C = ϖ C`, so
`c = ϖ • c₁`. The values of `c₁` are divisible by `u ϖⁿ⁻¹`, because `R` is a
domain.
