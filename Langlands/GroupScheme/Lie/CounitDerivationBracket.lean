import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-! # The convolution Lie algebra of counit derivations -/

noncomputable section

open WithConv Coalgebra TensorProduct
open scoped TensorProduct

namespace Langlands.GroupScheme.Lie

section Bialgebra

variable {R B A : Type*} [CommRing R] [CommRing B] [Bialgebra R B]
  [CommRing A] [Algebra R A]

local notation "C₁" => WithConv (B →ₗ[R] A)
local notation "C₂" => WithConv (B ⊗[R] B →ₗ[R] A)

private def tensorConv (f g : C₁) : C₂ :=
  toConv ((Algebra.TensorProduct.productMap (AlgHom.id R A) (AlgHom.id R A)).toLinearMap.comp
    (TensorProduct.map f.ofConv g.ofConv))

private theorem tensorConv_tmul (f g : C₁) (x y : B) :
    tensorConv f g (x ⊗ₜ[R] y) = f x * g y := by
  simp [tensorConv, Algebra.TensorProduct.productMap_apply_tmul]

private theorem tensorConv_mul (f g h j : C₁) :
    tensorConv f g * tensorConv h j = tensorConv (f * h) (g * j) := by
  let m := Algebra.TensorProduct.productMap (AlgHom.id R A) (AlgHom.id R A)
  have hh : toConv (TensorProduct.map f.ofConv g.ofConv) *
      toConv (TensorProduct.map h.ofConv j.ofConv) =
        toConv (TensorProduct.map (f * h).ofConv (g * j).ofConv) :=
    TensorProduct.map_convMul_map
  have hh' : (toConv (TensorProduct.map f.ofConv g.ofConv) *
      toConv (TensorProduct.map h.ofConv j.ofConv)).ofConv =
        TensorProduct.map (f * h).ofConv (g * j).ofConv := congrArg ofConv hh
  apply ofConv_injective
  change (tensorConv f g * tensorConv h j).ofConv =
    m.toLinearMap.comp (TensorProduct.map (f * h).ofConv (g * j).ofConv)
  rw [← hh', LinearMap.algHom_comp_convMul_distrib]
  rfl

private theorem tensorConv_sub_left (f g h : C₁) :
    tensorConv (f - g) h = tensorConv f h - tensorConv g h := by
  apply ofConv_injective
  apply TensorProduct.ext'
  intro x y
  change tensorConv (f - g) h (x ⊗ₜ[R] y) =
    tensorConv f h (x ⊗ₜ[R] y) - tensorConv g h (x ⊗ₜ[R] y)
  simp only [tensorConv_tmul, ofConv_sub, LinearMap.sub_apply, sub_mul]

private theorem tensorConv_sub_right (f g h : C₁) :
    tensorConv f (g - h) = tensorConv f g - tensorConv f h := by
  apply ofConv_injective
  apply TensorProduct.ext'
  intro x y
  change tensorConv f (g - h) (x ⊗ₜ[R] y) =
    tensorConv f g (x ⊗ₜ[R] y) - tensorConv f h (x ⊗ₜ[R] y)
  simp only [tensorConv_tmul, ofConv_sub, LinearMap.sub_apply, mul_sub]

/-- The Leibniz rule for an `R`-linear map into `A`, with the action of `B`
through the counit and the scalar map `R → A`. The convolution unit is this counit. -/
def IsCounitDerivation (f : C₁) : Prop :=
  ∀ x y, f (x * y) = f x * (1 : C₁) y + (1 : C₁) x * f y

private def mulPull (f : C₁) : C₂ :=
  toConv (f.ofConv.comp (Bialgebra.mulCoalgHom R B).toLinearMap)

private theorem mulPull_tmul (f : C₁) (x y : B) : mulPull f (x ⊗ₜ[R] y) = f (x * y) := rfl

private theorem mulPull_mul (f g : C₁) : mulPull (f * g) = mulPull f * mulPull g := by
  unfold mulPull
  rw [LinearMap.convMul_comp_coalgHom_distrib, toConv_ofConv]

private theorem mulPull_sub (f g : C₁) : mulPull (f - g) = mulPull f - mulPull g := by
  simp only [mulPull, ofConv_sub, LinearMap.sub_comp, toConv_sub]

private theorem isCounitDerivation_iff_mulPull (f : C₁) :
    IsCounitDerivation f ↔ mulPull f = tensorConv f 1 + tensorConv 1 f := by
  constructor
  · intro hf
    apply ofConv_injective
    apply TensorProduct.ext'
    intro x y
    change mulPull f (x ⊗ₜ[R] y) = tensorConv f 1 (x ⊗ₜ[R] y) + tensorConv 1 f (x ⊗ₜ[R] y)
    rw [mulPull_tmul, tensorConv_tmul, tensorConv_tmul]
    exact hf x y
  · intro hf x y
    have h := congrArg (fun q : C₂ => q (x ⊗ₜ[R] y)) hf
    change mulPull f (x ⊗ₜ[R] y) = tensorConv f 1 (x ⊗ₜ[R] y) + tensorConv 1 f (x ⊗ₜ[R] y) at h
    rwa [mulPull_tmul, tensorConv_tmul, tensorConv_tmul] at h

theorem IsCounitDerivation.commutator {f g : C₁}
    (hf : IsCounitDerivation f) (hg : IsCounitDerivation g) : IsCounitDerivation (f * g - g * f) := by
  rw [isCounitDerivation_iff_mulPull] at hf hg ⊢
  simp only [mulPull_sub, mulPull_mul, hf, hg, tensorConv_sub_left, tensorConv_sub_right,
    add_mul, mul_add, tensorConv_mul, one_mul, mul_one]
  abel

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R B A) in
/-- Counit derivations form a Lie subalgebra of the full convolution algebra;
no finite-dimensional or flatness hypothesis on the bialgebra is needed. -/
def counitDerivationLie : LieSubalgebra A C₁ where
  carrier := {f | IsCounitDerivation f}
  zero_mem' := fun x y => by change (0 : A) = _; simp
  add_mem' := by
    intro f g hf hg x y
    change f (x * y) + g (x * y) = (f x + g x) * (1 : C₁) y + (1 : C₁) x * (f y + g y)
    rw [(show IsCounitDerivation f from hf) x y, (show IsCounitDerivation g from hg) x y]
    ring
  smul_mem' := by
    intro a f hf x y
    change a * f (x * y) = a * f x * (1 : C₁) y + (1 : C₁) x * (a * f y)
    rw [(show IsCounitDerivation f from hf) x y]
    ring
  lie_mem' := fun hf hg => IsCounitDerivation.commutator hf hg

@[simp] theorem mem_counitDerivationLie (f : C₁) :
    f ∈ counitDerivationLie R B A ↔ IsCounitDerivation f := Iff.rfl

theorem counitDerivationLie_coe_lie (f g : counitDerivationLie R B A) :
    ((⁅f, g⁆ : counitDerivationLie R B A) : C₁) = (f : C₁) * g - (g : C₁) * f := rfl

end Bialgebra

end Langlands.GroupScheme.Lie
