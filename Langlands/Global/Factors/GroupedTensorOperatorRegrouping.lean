import Langlands.Global.Factors.GroupedTensorScalarEvaluation
import Langlands.Representation.Tensor.FiniteSlotDensity

/-! # Comparing operators before and after regrouping tensors by block -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option Elab.async false

universe u v w x y

namespace Langlands.Global.CuspidalBlockInduction

open Function

variable {I : Type u} {J : Type v}
variable {A : I → Type w} {C : J → I → Type x}
variable [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
variable [∀ p i, AddCommGroup (C p i)] [∀ p i, Module ℂ (C p i)]

local notation "A₀" => (⨂[ℂ] i, A i)
local notation "C₀" => (⨂[ℂ] p, (⨂[ℂ] i, C p i))
local notation "G" => (A₀ ⊗[ℂ] C₀)

private theorem groupedTensor_ext [Finite J] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {L R : G →ₗ[ℂ] V} (h : ∀ a c, L (groupedPure a c) = R (groupedPure a c)) : L = R := by
  let t := TensorProduct.mk ℂ A₀ C₀
  apply TensorProduct.ext'
  intro a c
  have ha : L.comp (t.flip c) = R.comp (t.flip c) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro b
    have hc : L.comp (t (PiTensorProduct.tprod ℂ b)) = R.comp (t (PiTensorProduct.tprod ℂ b)) := by
      refine PiTensorProduct.ext_of_span_eq_top
        (g := fun {p} (v : (i : I) → C p i) => PiTensorProduct.tprod ℂ v)
        (fun _ => PiTensorProduct.span_tprod_eq_top) ?_
      exact h b
    exact LinearMap.congr_fun hc c
  exact LinearMap.congr_fun ha a

/-- Acting in all slots of the finite factor and the nested place-by-block factor. -/
def groupedOperator (α : ∀ i, Module.End ℂ (A i)) (β : ∀ p i, Module.End ℂ (C p i)) :
    Module.End ℂ G :=
  TensorProduct.map (PiTensorProduct.map α) (PiTensorProduct.map fun p => PiTensorProduct.map (β p))

variable {W : I → Type y} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

local notation "W₀" => (⨂[ℂ] i, W i)

/-- Independent factor operators intertwine under regrouping if they have the
specified covariance after the individual block identifications. -/
theorem groupedOperator_intertwines [Finite J]
    (L : G →ₗ[ℂ] W₀)
    (e : ∀ i, A i ⊗[ℂ] (⨂[ℂ] p, C p i) →ₗ[ℂ] W i)
    (hL : ∀ (a : ∀ i, A i) (c : ∀ p i, C p i), L (groupedPure a c) =
      PiTensorProduct.tprod ℂ (fun i => e i (a i ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun p => c p i))))
    (α : ∀ i, Module.End ℂ (A i)) (β : ∀ p i, Module.End ℂ (C p i))
    (γ : ∀ i, Module.End ℂ (W i))
    (h : ∀ i a c, e i (α i a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun p => β p i (c p))) =
      γ i (e i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c))) :
    L.comp (groupedOperator α β) = (PiTensorProduct.map γ).comp L := by
  apply groupedTensor_ext
  intro a c
  change L (groupedOperator α β (groupedPure a c)) = PiTensorProduct.map γ (L (groupedPure a c))
  have he : groupedOperator α β (groupedPure a c) =
      groupedPure (fun i => α i (a i)) (fun p i => β p i (c p i)) := by
    simp only [groupedOperator, groupedPure, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rw [he, hL, hL, PiTensorProduct.map_tprod]
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext i
  exact h i (a i) (fun p => c p i)

variable [DecidableEq I] [DecidableEq J]

/-- The sum of the individual block actions in a single place-slot. -/
def groupedPlaceOperator [Fintype I] (p : J) (D : ∀ i, Module.End ℂ (C p i)) :
    Module.End ℂ C₀ :=
  FiniteTensor.slotAlgebraHom p (∑ i, FiniteTensor.slotAlgebraHom i (D i))

private theorem slotAlgebraHom_tprod {Z : J → Type*}
    [∀ p, AddCommGroup (Z p)] [∀ p, Module ℂ (Z p)]
    (p : J) (D : Module.End ℂ (Z p)) (z : ∀ p, Z p) :
    FiniteTensor.slotAlgebraHom p D (PiTensorProduct.tprod ℂ z) =
      PiTensorProduct.tprod ℂ (update z p (D (z p))) := by
  have h := FiniteTensor.map_slot_tprod_update p D z (z p)
  rw [update_eq_self] at h
  exact h

/-- A one-place sum of block derivatives becomes the sum of the corresponding
operators on the regrouped block tensor. -/
theorem groupedPlaceOperator_intertwines [Fintype I] [Finite J]
    (L : G →ₗ[ℂ] W₀)
    (e : ∀ i, A i ⊗[ℂ] (⨂[ℂ] p, C p i) →ₗ[ℂ] W i)
    (hL : ∀ (a : ∀ i, A i) (c : ∀ p i, C p i), L (groupedPure a c) =
      PiTensorProduct.tprod ℂ (fun i => e i (a i ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun p => c p i))))
    (p : J) (D : ∀ i, Module.End ℂ (C p i)) (E : ∀ i, Module.End ℂ (W i))
    (h : ∀ i a c, e i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (update c p (D i (c p)))) =
      E i (e i (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c))) :
    L.comp ((groupedPlaceOperator p D).lTensor A₀) =
      (∑ i, FiniteTensor.slotAlgebraHom i (E i)).comp L := by
  apply groupedTensor_ext
  intro a c
  change L ((groupedPlaceOperator p D).lTensor A₀ (groupedPure a c)) =
    (∑ i, FiniteTensor.slotAlgebraHom i (E i)) (L (groupedPure a c))
  simp only [groupedPure, groupedPlaceOperator, LinearMap.lTensor_tmul, map_sum, LinearMap.sum_apply,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  let c' := update c p (update (c p) i (D i (c p i)))
  have hc : FiniteTensor.slotAlgebraHom p (FiniteTensor.slotAlgebraHom i (D i))
      (PiTensorProduct.tprod ℂ (fun q => PiTensorProduct.tprod ℂ (c q))) =
      PiTensorProduct.tprod ℂ (fun q => PiTensorProduct.tprod ℂ (c' q)) := by
    rw [slotAlgebraHom_tprod, slotAlgebraHom_tprod]
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext q
    by_cases hq : q = p
    · subst q
      simp only [c', update_self]
    · simp only [c', update_of_ne hq]
  rw [hc]
  change L (groupedPure a c') = FiniteTensor.slotAlgebraHom i (E i) (L (groupedPure a c))
  rw [hL a c', hL a c]
  rw [slotAlgebraHom_tprod]
  apply congrArg (PiTensorProduct.tprod ℂ)
  funext j
  by_cases hj : j = i
  · subst j
    simp only [update_self]
    have he : (fun q => c' q i) = update (fun q => c q i) p (D i (c p i)) := by
      funext q
      by_cases hq : q = p
      · subst q
        simp only [c', update_self]
      · simp only [c', update_of_ne hq]
    rw [he]
    exact h i (a i) (fun q => c q i)
  · rw [update_of_ne hj]
    have he : (fun q => c' q j) = fun q => c q j := by
      funext q
      by_cases hq : q = p
      · subst q
        simp only [c', update_self, update_of_ne hj]
      · simp only [c', update_of_ne hq]
    rw [he]

end Langlands.Global.CuspidalBlockInduction
