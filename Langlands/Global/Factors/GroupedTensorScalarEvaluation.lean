import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.Basic.Complex.Basic

/-! # Scalar evaluation on tensors grouped by two indices -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

universe u v w x

namespace Langlands.Global.CuspidalBlockInduction

variable {I : Type u} {J : Type v}
variable {A : I → Type w} {C : J → I → Type x}
variable [∀ i, AddCommMonoid (A i)] [∀ i, Module ℂ (A i)]
variable [∀ p i, AddCommMonoid (C p i)] [∀ p i, Module ℂ (C p i)]

local notation "A₀" => (⨂[ℂ] i, A i)
local notation "C₀" => (⨂[ℂ] p, (⨂[ℂ] i, C p i))

/-- Insert a finite family and a nested family as a pure grouped tensor. -/
def groupedPure (a : ∀ i, A i) (c : ∀ p i, C p i) : A₀ ⊗[ℂ] C₀ :=
  PiTensorProduct.tprod ℂ a ⊗ₜ[ℂ]
    PiTensorProduct.tprod ℂ (fun p => PiTensorProduct.tprod ℂ (c p))

private theorem grouped_ext [Finite J]
    {L R : A₀ ⊗[ℂ] C₀ →ₗ[ℂ] ℂ}
    (h : ∀ a c, L (groupedPure a c) = R (groupedPure a c)) : L = R := by
  let t := TensorProduct.mk ℂ A₀ C₀
  apply TensorProduct.ext'
  intro a c
  have ha : L.comp (t.flip c) = R.comp (t.flip c) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro b
    have hc : L.comp (t (PiTensorProduct.tprod ℂ b)) =
        R.comp (t (PiTensorProduct.tprod ℂ b)) := by
      refine PiTensorProduct.ext_of_span_eq_top
        (g := fun {p} (v : (i : I) → C p i) => PiTensorProduct.tprod ℂ v)
        (fun _ => PiTensorProduct.span_tprod_eq_top) ?_
      exact h b
    exact LinearMap.congr_fun hc c
  exact LinearMap.congr_fun ha a

/-- Two factorizations of scalar evaluation on pure tensors give covariance
for arbitrary tensors as soon as each scalar factor has the specified law. -/
theorem groupedProductCovariance [Fintype I] [Finite J]
    (α : ∀ i, Module.End ℂ (A i)) (β : ∀ p i, Module.End ℂ (C p i))
    (L R : A₀ ⊗[ℂ] C₀ →ₗ[ℂ] ℂ)
    (l r : ∀ i, A i → (∀ p, C p i) → ℂ)
    (hL : ∀ a c, L (groupedPure a c) = ∏ i, l i (a i) (fun p => c p i))
    (hR : ∀ a c, R (groupedPure a c) = ∏ i, r i (a i) (fun p => c p i))
    (h : ∀ i a c, l i (α i a) (fun p => β p i (c p)) = r i a c)
    (a : A₀) (c : C₀) :
    L (PiTensorProduct.map α a ⊗ₜ[ℂ] PiTensorProduct.map (fun p => PiTensorProduct.map (β p)) c) =
      R (a ⊗ₜ[ℂ] c) := by
  let U := TensorProduct.map (PiTensorProduct.map α)
    (PiTensorProduct.map fun p => PiTensorProduct.map (β p))
  have hp (a : ∀ i, A i) (c : ∀ p i, C p i) :
      U (groupedPure a c) = groupedPure (fun i => α i (a i)) (fun p i => β p i (c p i)) := by
    simp only [U, groupedPure, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  have he : L.comp U = R := by
    apply grouped_ext
    intro a c
    change L (U (groupedPure a c)) = R (groupedPure a c)
    rw [hp, hL, hR]
    exact Finset.prod_congr rfl (fun i _ => h i (a i) (fun p => c p i))
  exact (congrArg L (TensorProduct.map_tmul _ _ a c)).symm.trans
    (LinearMap.congr_fun he (a ⊗ₜ[ℂ] c))

/-- Grouped scalar covariance when the action is confined to the first family. -/
theorem groupedProductCovariance_first [Fintype I] [Finite J]
    (α : ∀ i, Module.End ℂ (A i)) (L R : A₀ ⊗[ℂ] C₀ →ₗ[ℂ] ℂ)
    (l r : ∀ i, A i → (∀ p, C p i) → ℂ)
    (hL : ∀ a c, L (groupedPure a c) = ∏ i, l i (a i) (fun p => c p i))
    (hR : ∀ a c, R (groupedPure a c) = ∏ i, r i (a i) (fun p => c p i))
    (h : ∀ i a c, l i (α i a) c = r i a c)
    (a : A₀) (c : C₀) :
    L (PiTensorProduct.map α a ⊗ₜ[ℂ] c) = R (a ⊗ₜ[ℂ] c) := by
  have he := groupedProductCovariance α (fun _ _ => LinearMap.id) L R l r hL hR h a c
  simpa only [PiTensorProduct.map_id, LinearMap.id_apply] using he

/-- Grouped scalar covariance when the action is confined to the nested family. -/
theorem groupedProductCovariance_second [Fintype I] [Finite J]
    (β : ∀ p i, Module.End ℂ (C p i)) (L R : A₀ ⊗[ℂ] C₀ →ₗ[ℂ] ℂ)
    (l r : ∀ i, A i → (∀ p, C p i) → ℂ)
    (hL : ∀ a c, L (groupedPure a c) = ∏ i, l i (a i) (fun p => c p i))
    (hR : ∀ a c, R (groupedPure a c) = ∏ i, r i (a i) (fun p => c p i))
    (h : ∀ i a c, l i a (fun p => β p i (c p)) = r i a c)
    (a : A₀) (c : C₀) :
    L (a ⊗ₜ[ℂ] PiTensorProduct.map (fun p => PiTensorProduct.map (β p)) c) =
      R (a ⊗ₜ[ℂ] c) := by
  have he := groupedProductCovariance (fun _ => LinearMap.id) β L R l r hL hR h a c
  simpa only [PiTensorProduct.map_id, LinearMap.id_apply] using he

end Langlands.Global.CuspidalBlockInduction
