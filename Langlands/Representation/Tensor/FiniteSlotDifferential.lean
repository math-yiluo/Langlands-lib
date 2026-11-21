import Langlands.Representation.Tensor.FiniteSlotDensity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic

/-! # Scalar differentiation of a one-slot tensor action -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

universe u v w

namespace Langlands.FiniteTensor

open Function

variable {I : Type u} [DecidableEq I] {G : I → Type v} [∀ i, Group (G i)]
variable {V : I → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The external tensor representation at a group element supported in one slot. -/
def externalSlot (ρ : ∀ i, Representation ℂ (G i) (V i)) (i : I) :
    Representation ℂ (G i) (⨂[ℂ] j, V j) :=
  ((slotAlgebraHom (V := V) i).toMonoidHom).comp (ρ i)

theorem external_mulSingle_eq_externalSlot (ρ : ∀ i, Representation ℂ (G i) (V i))
    (i : I) (g : G i) : external ρ (Pi.mulSingle i g) = externalSlot ρ i g := by
  change PiTensorProduct.map (fun j => ρ j (Pi.mulSingle i g j)) =
    PiTensorProduct.map (slot i (ρ i g))
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    rw [Pi.mulSingle_eq_same, slot, Function.update_self]
  · rw [Pi.mulSingle_eq_of_ne h, map_one, slot, Function.update_of_ne h]
    rfl

/-- Scalar differentiation in a single tensor slot is the tensor of the
local derivative with the identities on the other factors. -/
theorem hasDerivAt_externalSlot (ρ : ∀ i, Representation ℂ (G i) (V i)) (i : I)
    (γ : ℝ → G i) (D : Module.End ℂ (V i))
    (hD : ∀ (x : V i) (ℓ : V i →ₗ[ℂ] ℂ),
      HasDerivAt (fun t => ℓ (ρ i (γ t) x)) (ℓ (D x)) 0)
    (x : ⨂[ℂ] j, V j) (ℓ : (⨂[ℂ] j, V j) →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => ℓ (externalSlot ρ i (γ t) x)) (ℓ (slotAlgebraHom i D x)) 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c b =>
    let J := (PiTensorProduct.tprod ℂ).toLinearMap b i
    have h (T : Module.End ℂ (V i)) :
        slotAlgebraHom i T (PiTensorProduct.tprod ℂ b) = J (T (b i)) := by
      change PiTensorProduct.map (slot i T) (PiTensorProduct.tprod ℂ b) =
        PiTensorProduct.tprod ℂ (update b i (T (b i)))
      conv_lhs => rw [← Function.update_eq_self i b]
      exact map_slot_tprod_update i T b (b i)
    have hd := hD (b i) (ℓ.comp J)
    change HasDerivAt (fun t => ℓ (slotAlgebraHom i (ρ i (γ t)) (c • PiTensorProduct.tprod ℂ b))) _ 0
    simp only [map_smul, h, smul_eq_mul, LinearMap.comp_apply] at hd ⊢
    exact hd.const_mul c
  | add a b ha hb =>
    simpa only [map_add] using! (HasDerivAt.fun_add ha hb)

end Langlands.FiniteTensor
