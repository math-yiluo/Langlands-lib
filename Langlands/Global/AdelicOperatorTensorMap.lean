import Langlands.Automorphic.FreeOperatorPlaceIntertwining
import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement
import Langlands.Global.AdelicOperatorTensorAction
import Langlands.Representation.Tensor.SmoothSubquotients

/-! # Intertwiners of adelic tensors from intertwiners at the places -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Classical TensorProduct

universe u

namespace Langlands.Global.AdelicOperatorTensor

open Langlands.Archimedean Langlands.Automorphic ArchimedeanGL Langlands.FiniteTensor

attribute [local instance 100] LieRing.ofAssociativeRing

private def liftMap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) : ULift.{u} V →ₗ[ℂ] ULift.{u} W :=
  ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap

private theorem liftMap_commutes {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {f : V →ₗ[ℂ] W} {A : Module.End ℂ V} {B : Module.End ℂ W}
    (h : ∀ x, f (A x) = B (f x)) (x : ULift.{u} V) :
    liftMap f (ULift.moduleEquiv.symm.conjAlgEquiv ℂ A x) =
      ULift.moduleEquiv.symm.conjAlgEquiv ℂ B (liftMap f x) :=
  congrArg ULift.up (h x.down)

private theorem piTensorMap_slot_commutes {I : Type*} [DecidableEq I]
    {V W : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (f : ∀ i, V i →ₗ[ℂ] W i) (i : I)
    (A : Module.End ℂ (V i)) (B : Module.End ℂ (W i))
    (h : ∀ x, f i (A x) = B (f i x)) (x : ⨂[ℂ] i, V i) :
    PiTensorProduct.map f (slotAlgebraHom i A x) =
      slotAlgebraHom i B (PiTensorProduct.map f x) := by
  change (PiTensorProduct.map f ∘ₗ PiTensorProduct.map (slot i A)) x =
    (PiTensorProduct.map (slot i B) ∘ₗ PiTensorProduct.map f) x
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 2
  funext j
  by_cases hj : j = i
  · subst j
    simp only [slot, Function.update_self]
    exact LinearMap.ext h
  · simp [slot, hj]

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation "CL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ

private def mapSlots {Vf Wf : Type u} {Vr Wr : RP → Type} {Vc Wc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Wf] [Module ℂ Wf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Wr v)] [∀ v, Module ℂ (Wr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    [∀ v, AddCommGroup (Wc v)] [∀ v, Module ℂ (Wc v)]
    (f : Vf →ₗ[ℂ] Wf) (fr : ∀ v : RP, Vr v →ₗ[ℂ] Wr v) (fc : ∀ v : CP, Vc v →ₗ[ℂ] Wc v)
    (i : Slot F) : SlotSpace F Vf Vr Vc i →ₗ[ℂ] SlotSpace F Wf Wr Wc i :=
  match i with
  | .inl _ => f
  | .inr (.inl v) => liftMap (fr v)
  | .inr (.inr v) => liftMap (fc v)

/-- Tensor a map of the finite adelic factors with the maps of the individual
real and complex factors. -/
def tensorMap {Vf Wf : Type u} {Vr Wr : RP → Type} {Vc Wc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Wf] [Module ℂ Wf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Wr v)] [∀ v, Module ℂ (Wr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    [∀ v, AddCommGroup (Wc v)] [∀ v, Module ℂ (Wc v)]
    (f : Vf →ₗ[ℂ] Wf) (fr : ∀ v : RP, Vr v →ₗ[ℂ] Wr v) (fc : ∀ v : CP, Vc v →ₗ[ℂ] Wc v) :
    Space F Vf Vr Vc →ₗ[ℂ] Space F Wf Wr Wc :=
  PiTensorProduct.map (mapSlots F f fr fc)

theorem tensorMap_injective {Vf Wf : Type u} {Vr Wr : RP → Type} {Vc Wc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Wf] [Module ℂ Wf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Wr v)] [∀ v, Module ℂ (Wr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    [∀ v, AddCommGroup (Wc v)] [∀ v, Module ℂ (Wc v)]
    {f : Vf →ₗ[ℂ] Wf} {fr : ∀ v : RP, Vr v →ₗ[ℂ] Wr v} {fc : ∀ v : CP, Vc v →ₗ[ℂ] Wc v}
    (hf : Function.Injective f) (hr : ∀ v, Function.Injective (fr v)) (hc : ∀ v, Function.Injective (fc v)) :
    Function.Injective (tensorMap F f fr fc) := by
  apply piTensorMap_injective
  rintro (_ | v | v)
  · exact hf
  · exact ULift.moduleEquiv.symm.injective.comp ((hr v).comp ULift.moduleEquiv.injective)
  · exact ULift.moduleEquiv.symm.injective.comp ((hc v).comp ULift.moduleEquiv.injective)

theorem tensorMap_surjective {Vf Wf : Type u} {Vr Wr : RP → Type} {Vc Wc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Wf] [Module ℂ Wf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Wr v)] [∀ v, Module ℂ (Wr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    [∀ v, AddCommGroup (Wc v)] [∀ v, Module ℂ (Wc v)]
    {f : Vf →ₗ[ℂ] Wf} {fr : ∀ v : RP, Vr v →ₗ[ℂ] Wr v} {fc : ∀ v : CP, Vc v →ₗ[ℂ] Wc v}
    (hf : Function.Surjective f) (hr : ∀ v, Function.Surjective (fr v)) (hc : ∀ v, Function.Surjective (fc v)) :
    Function.Surjective (tensorMap F f fr fc) := by
  apply piTensorMap_surjective
  rintro (_ | v | v)
  · exact hf
  · exact ULift.moduleEquiv.symm.surjective.comp ((hr v).comp ULift.moduleEquiv.surjective)
  · exact ULift.moduleEquiv.symm.surjective.comp ((hc v).comp ULift.moduleEquiv.surjective)

variable [NumberField F]

set_option maxHeartbeats 1500000 in
/-- Tensor the finite and archimedean intertwiners for the entire free action. -/
def tensorIntertwiningMap {Vf Wf : Type u} {Vr Wr : RP → Type} {Vc Wc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Wf] [Module ℂ Wf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Wr v)] [∀ v, Module ℂ (Wr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    [∀ v, AddCommGroup (Wc v)] [∀ v, Module ℂ (Wc v)]
    {fin : Representation ℂ (FiniteAdelicGL F n) Vf}
    {fin' : Representation ℂ (FiniteAdelicGL F n) Wf}
    {κr : ∀ v : RP, Representation ℂ RK (Vr v)}
    {κr' : ∀ v : RP, Representation ℂ RK (Wr v)}
    {δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v)}
    {δr' : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Wr v)}
    {κc : ∀ v : CP, Representation ℂ CK (Vc v)}
    {κc' : ∀ v : CP, Representation ℂ CK (Wc v)}
    {δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)}
    {δc' : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Wc v)}
    (f : fin.IntertwiningMap fin')
    (fr : ∀ v : RP, Vr v →ₗ[ℂ] Wr v) (fc : ∀ v : CP, Vc v →ₗ[ℂ] Wc v)
    (hr : ∀ v, fr v ∈ gkHoms (κr v) (δr v) (κr' v) (δr' v))
    (hc : ∀ v, fc v ∈ gkHoms (κc v) (δc v) (κc' v) (δc' v)) :
    Representation.IntertwiningMap (tensorFreeAction F n fin κr δr κc δc).toMonoidHom
      (tensorFreeAction F n fin' κr' δr' κc' δc').toMonoidHom := by
  let φ := tensorMap F f.toLinearMap fr fc
  refine φ.intertwiningMap_of_isIntertwiningMap _ _ ?_
  refine intertwines_freeActionOfOperators_of_places F n φ
    (fun d => slotAlgebraHom (.inl ()) (V := SlotSpace F Vf Vr Vc) (fin d))
    (fun d => slotAlgebraHom (.inl ()) (V := SlotSpace F Wf Wr Wc) (fin' d))
    (tensorCompactAction F n (Vf := Vf) κr κc) (tensorCompactAction F n (Vf := Wf) κr' κc')
    (UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Vf) δr δc))
    (UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Wf) δr' δc'))
    ?_ ?_ ?_ ?_ ?_
  · intro d x
    exact piTensorMap_slot_commutes (mapSlots F f.toLinearMap fr fc) (.inl ()) _ _
      (Representation.IntertwiningMap.isIntertwining fin fin' f d) x
  · intro v k x
    simp only [tensorCompactAction_realPlace]
    exact piTensorMap_slot_commutes (mapSlots F f.toLinearMap fr fc) (.inr (.inl v)) _ _
      (liftMap_commutes ((hr v).1 k)) x
  · intro v k x
    simp only [tensorCompactAction_complexPlace]
    exact piTensorMap_slot_commutes (mapSlots F f.toLinearMap fr fc) (.inr (.inr v)) _ _
      (liftMap_commutes ((hc v).1 k)) x
  · intro v X x
    simp only [envelopingGenerator, UniversalEnvelopingAlgebra.lift_ι_apply, tensorLieAction_realPlace]
    exact piTensorMap_slot_commutes (mapSlots F f.toLinearMap fr fc) (.inr (.inl v)) _ _
      (liftMap_commutes ((hr v).2 X)) x
  · intro v X x
    simp only [envelopingGenerator, UniversalEnvelopingAlgebra.lift_ι_apply, tensorLieAction_complexPlace]
    exact piTensorMap_slot_commutes (mapSlots F f.toLinearMap fr fc) (.inr (.inr v)) _ _
      (liftMap_commutes ((hc v).2 X)) x

end Langlands.Global.AdelicOperatorTensor
