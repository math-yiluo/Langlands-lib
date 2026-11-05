# Minimal relations among primitive elements are additive

Author: Worker 1519, as internal infrastructure for the proof of
`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorStatement`.

Provenance: internal. The statement that a minimal-degree element of the kernel of
`k[Y₁, …, Yₛ] → A`, `Yᵢ ↦ yᵢ` with all `yᵢ` primitive, is an additive polynomial is a
standard observation about Hopf ideals; the formal argument is the author's own, and no
source statement is translated.

Throughout `k` is a field and polynomials are `MvPolynomial (Fin s) k`.

## The additivity defect

- `addComul`: the `k`-algebra map `k[Y] → k[Y] ⊗ k[Y]`, `Yᵢ ↦ Yᵢ ⊗ 1 + 1 ⊗ Yᵢ`
  (`addComul_X`). It is the comultiplication making the variables primitive; no bialgebra
  instance on `MvPolynomial` is introduced.
- `addDefect`: the `k`-linear map `F ↦ addComul F - F ⊗ 1 - 1 ⊗ F` (`addDefect_apply`).
- `addDefect_mul_X`: `addDefect (P * Yᵢ) = P ⊗ Yᵢ + Yᵢ ⊗ P +
  addDefect P * (Yᵢ ⊗ 1 + 1 ⊗ Yᵢ)`; `addDefect_X`: `addDefect Yᵢ = 0`.
- `lowTensor m`: the image of `L ⊗ L → k[Y] ⊗ k[Y]` for `L` the polynomials of total
  degree at most `m` (`restrictTotalDegree`). `tmul_mem_lowTensor`, `lowTensor_mono` and
  `mul_mem_lowTensor` (multiplication by `Yᵢ ⊗ 1 + 1 ⊗ Yᵢ` raises `m` by one) are proved
  from `TensorProduct.range_map_eq_span_tmul`.
- `addDefect_monomial_mem n α hα`: for a monomial of degree `n + 1`, the defect lies in
  `lowTensor n`. Induction on `n`, splitting off one variable.
- `addDefect_mem_lowTensor`: if `F` has total degree at most `d + 1` and constant
  coefficient `0`, its defect lies in `lowTensor d`.
- `aeval_add_of_addDefect_eq_zero`: if `addDefect F = 0`, then
  `aeval (u + v) F = aeval u F + aeval v F` for all `u v : Fin s → R` and every commutative
  `k`-algebra `R` (apply the algebra map `k[Y] ⊗ k[Y] → R` given by `u` and `v`).

## Polynomials in primitive elements

Let `A` be a commutative `k`-bialgebra and `y : Fin s → A` a family of primitive elements.

- `comul_aeval_primitive`: `comul (aeval y F)` is the image of `addComul F` under
  `aeval y ⊗ aeval y`.
- `counit_aeval_primitive`: `counit (aeval y F) = constantCoeff F`.
- `addDefect_eq_zero_of_minimal hy hF hmin` (**minimal relations are additive**): if
  `aeval y F = 0` and every relation of smaller total degree is zero, then
  `addDefect F = 0`.

  Proof as implemented. The constant coefficient vanishes by the counit. If the degree is
  `0`, then `F = 0`. Otherwise the defect equals `(ι ⊗ ι) t` for some `t` in the tensor square
  of the polynomials of degree below that of `F`. On those polynomials `aeval y` is injective
  by minimality, so `(aeval y ∘ ι) ⊗ (aeval y ∘ ι)` is injective
  (`TensorProduct.map_injective_of_flat_flat`; modules over a field are flat). Its value at
  `t` is the image of the defect in `A ⊗ A`, which is
  `comul (aeval y F) - aeval y F ⊗ 1 - 1 ⊗ aeval y F = 0`. Hence `t = 0`.
