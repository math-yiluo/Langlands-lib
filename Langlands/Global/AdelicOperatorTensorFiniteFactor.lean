import Langlands.Automorphic.ArchimedeanPlaceOperatorFamily
import Langlands.Global.AdelicOperatorTensor
import Langlands.Representation.Tensor.FiniteSlotDensity

/-! # Splitting off the finite factor of the adelic operator tensor -/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicOperatorTensor

open Automorphic InfinitePlaceFamily FiniteTensor

variable (F : Type u) [Field F] [NumberField F]
variable {Af : Type u} [AddCommGroup Af] [Module ℂ Af]
variable (V : Index F → Type) [∀ p, AddCommGroup (V p)] [∀ p, Module ℂ (V p)]

local notation "Vr" => (fun v => V (Sum.inl v))
local notation "Vc" => (fun v => V (Sum.inr v))
local notation "Slots" => SlotSpace F Af Vr Vc
local notation "Source" => Space F Af Vr Vc
local notation "InfiniteTensor" => (⨂[ℂ] p, V p)

/-- The infinite tensor slot is the universe lift of its place module. -/
def infiniteSlotEquiv (p : Index F) : Slots (.inr p) ≃ₗ[ℂ] V p := by
  cases p <;> exact ULift.moduleEquiv

/-- Split the finite slot from the infinite tensor and remove the universe
lifts from the individual infinite factors. -/
def splitFiniteTensor : Source ≃ₗ[ℂ] Af ⊗[ℂ] InfiniteTensor :=
  (PiTensorProduct.tmulEquivDep ℂ Slots).symm.trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv (s := fun i : Unit => Slots (.inl i)) ())
      (PiTensorProduct.congr (infiniteSlotEquiv F (Af := Af) V)))

theorem splitFiniteTensor_tprod (x : ∀ i, Slots i) :
    splitFiniteTensor F V (PiTensorProduct.tprod ℂ x) =
      x (.inl ()) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun p => infiniteSlotEquiv F V p (x (.inr p))) := by
  simp only [splitFiniteTensor, LinearEquiv.trans_apply, PiTensorProduct.tmulEquivDep_symm_apply,
    TensorProduct.congr_tmul, PiTensorProduct.congr_tprod]
  exact congrArg (fun a : Af => a ⊗ₜ[ℂ]
    (PiTensorProduct.tprod ℂ fun p => infiniteSlotEquiv F V p (x (.inr p))))
    (PiTensorProduct.subsingletonEquiv_apply_tprod () (fun i : Unit => x (.inl i)))

private theorem splitFiniteTensor_map (A : ∀ i, Module.End ℂ (Slots i)) (x : Source) :
    splitFiniteTensor F V (PiTensorProduct.map A x) =
      TensorProduct.map (A (.inl ()))
        (PiTensorProduct.map (fun p => (infiniteSlotEquiv F V p).conjAlgEquiv ℂ (A (.inr p))))
        (splitFiniteTensor F V x) := by
  let E := (splitFiniteTensor F (Af := Af) V).toLinearMap
  let L := TensorProduct.map (A (.inl ()))
    (PiTensorProduct.map (fun p => (infiniteSlotEquiv F V p).conjAlgEquiv ℂ (A (.inr p))))
  have h : E.comp (PiTensorProduct.map A) = L.comp E := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro y
    change splitFiniteTensor F V (PiTensorProduct.map A (PiTensorProduct.tprod ℂ y)) =
      L (splitFiniteTensor F V (PiTensorProduct.tprod ℂ y))
    simp only [PiTensorProduct.map_tprod, splitFiniteTensor_tprod, L, TensorProduct.map_tmul,
      LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply congrArg (TensorProduct.mk ℂ Af InfiniteTensor (A (.inl ()) (y (.inl ()))))
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext p
    let e := infiniteSlotEquiv F (Af := Af) V p
    exact congrArg (fun t => e (A (.inr p) t)) (e.symm_apply_apply (y (.inr p))).symm
  exact LinearMap.congr_fun h x

/-- An operator in the finite slot acts on the left factor after splitting. -/
theorem splitFiniteTensor_finite (A : Module.End ℂ Af) (x : Source) :
    splitFiniteTensor F V ((slotAlgebraHom (.inl ()) (V := Slots) A) x) =
      A.rTensor InfiniteTensor (splitFiniteTensor F V x) := by
  let L := slot (.inl ()) (V := Slots) A
  have hleft : L (.inl ()) = A := Function.update_self ..
  have hright (p : Index F) :
      (infiniteSlotEquiv F (Af := Af) V p).conjAlgEquiv ℂ (L (.inr p)) = LinearMap.id := by
    have h : L (.inr p) = 1 := by
      simp [L, slot, ← Module.End.one_eq_id]
    rw [h, map_one, Module.End.one_eq_id]
  change splitFiniteTensor F V (PiTensorProduct.map L x) = _
  rw [splitFiniteTensor_map, hleft, funext hright, PiTensorProduct.map_id]
  rfl

/-- An operator at one infinite place acts on that slot of the right factor
after splitting and removing the universe lift. -/
theorem splitFiniteTensor_infinite (p : Index F) (A : Module.End ℂ (V p)) (x : Source) :
    splitFiniteTensor F V
      ((slotAlgebraHom (.inr p) (V := Slots) ((infiniteSlotEquiv F V p).symm.conjAlgEquiv ℂ A)) x) =
      (slotAlgebraHom p A).lTensor Af (splitFiniteTensor F V x) := by
  let D := infiniteSlotEquiv F (Af := Af) V p
  let L := slot (.inr p) (V := Slots) (D.symm.conjAlgEquiv ℂ A)
  have hleft : L (.inl ()) = LinearMap.id := by simp [L, slot]
  have hright (q : Index F) :
      (infiniteSlotEquiv F (Af := Af) V q).conjAlgEquiv ℂ (L (.inr q)) = slot p A q := by
    by_cases hq : q = p
    · subst q
      change D.conjAlgEquiv ℂ (L (.inr p)) = _
      have hp : L (.inr p) = D.symm.conjAlgEquiv ℂ A := Function.update_self ..
      rw [hp, ← LinearEquiv.symm_conjAlgEquiv, AlgEquiv.apply_symm_apply]
      simp [slot]
    · have hqp : (Sum.inr q : Slot F) ≠ .inr p := fun h => hq (Sum.inr.inj h)
      have h : L (.inr q) = 1 := by
        simp [L, slot, hqp, ← Module.End.one_eq_id]
      rw [h, map_one, Module.End.one_eq_id]
      simp [slot, hq]
  change splitFiniteTensor F V (PiTensorProduct.map L x) = _
  rw [splitFiniteTensor_map, hleft, funext hright]
  rfl

end Langlands.Global.AdelicOperatorTensor
