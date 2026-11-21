import Langlands.Global.AdelicOperatorTensor
import Langlands.Global.ArchimedeanPlaceEnveloping

/-! # The free operator action on the adelic tensor -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical TensorProduct

universe u

namespace Langlands.Global.AdelicOperatorTensor

open NumberField Langlands.Archimedean Langlands.Automorphic ArchimedeanGL Langlands.FiniteTensor

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem slotAlgebraHom_commute {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] {i j : I} (h : i ≠ j)
    (A : Module.End ℂ (V i)) (B : Module.End ℂ (V j)) :
    Commute (slotAlgebraHom i A) (slotAlgebraHom j B) := by
  change PiTensorProduct.map (slot i A) * PiTensorProduct.map (slot j B) =
    PiTensorProduct.map (slot j B) * PiTensorProduct.map (slot i A)
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [slot, h, ← Module.End.one_eq_id]
  by_cases hj : k = j
  · subst k
    simp [slot, hi, ← Module.End.one_eq_id]
  simp [slot, hi, hj]

private def sumSlotLieAction {I L : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℂ L]
    {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (d : ∀ i, L →ₗ⁅ℂ⁆ Module.End ℂ (V i)) : L →ₗ⁅ℂ⁆ Module.End ℂ (⨂[ℂ] i, V i) where
  toLinearMap := ∑ i, (slotAlgebraHom i).toLinearMap.comp (d i).toLinearMap
  map_lie' := by
    intro X Y
    let D : L →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
      ∑ i, (slotAlgebraHom i).toLinearMap.comp (d i).toLinearMap
    change D ⁅X, Y⁆ = ⁅D X, D Y⁆
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      D, LieHom.coe_toLinearMap, LieHom.map_lie, ← AlgHom.toLieHom_apply,
      sum_lie, lie_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · intro j _ hij
      exact (slotAlgebraHom_commute hij (d j X) (d i Y)).lie_eq
    · simp

private theorem sumSlotLieAction_apply {I L : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℂ L]
    {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (d : ∀ i, L →ₗ⁅ℂ⁆ Module.End ℂ (V i)) (X : L) :
    sumSlotLieAction d X = ∑ i, slotAlgebraHom i (d i X) := by
  change (∑ i, (slotAlgebraHom i).toLinearMap.comp (d i).toLinearMap) X = _
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LieHom.coe_toLinearMap]

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation "CL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ

private theorem realProjection_realPlace (v w : RP) (X : RL) :
    realPlaceComplexLieProjection F n w (realPlaceComplexLieInclusion F n v X) =
      if w = v then X else 0 := by
  by_cases h : w = v
  · subst w
    simp
  · rw [ite_eq_right h]
    induction X using TensorProduct.inductionOn with
    | tmul z X => simp [Pi.single_eq_of_ne h]
    | add X Y hX hY => simp [hX, hY]

private theorem complexProjection_complexPlace (v w : CP) (X : CL) :
    complexPlaceComplexLieProjection F n w (complexPlaceComplexLieInclusion F n v X) =
      if w = v then X else 0 := by
  by_cases h : w = v
  · subst w
    simp
  · rw [ite_eq_right h]
    induction X using TensorProduct.inductionOn with
    | tmul z X => simp [Pi.single_eq_of_ne h]
    | add X Y hX hY => simp [hX, hY]

private theorem realProjection_complexPlace (v : RP) (w : CP) (X : CL) :
    realPlaceComplexLieProjection F n v (complexPlaceComplexLieInclusion F n w X) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simp [hX, hY]

private theorem complexProjection_realPlace (v : CP) (w : RP) (X : RL) :
    complexPlaceComplexLieProjection F n v (realPlaceComplexLieInclusion F n w X) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => simp
  | add X Y hX hY => simp [hX, hY]

section Actions

variable [NumberField F]

private def placeLieAction {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)) (i : Slot F) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (SlotSpace F Vf Vr Vc i) :=
  match i with
  | .inl _ => 0
  | .inr (.inl v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toLieHom.comp
      ((δr v).comp (realPlaceComplexLieProjection F n v))
  | .inr (.inr v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toLieHom.comp
      ((δc v).comp (complexPlaceComplexLieProjection F n v))

/-- The global Lie algebra acts by the sum of the actions of its place projections. -/
def tensorLieAction {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (Space F Vf Vr Vc) :=
  sumSlotLieAction (placeLieAction F n (Vf := Vf) δr δc)

set_option maxHeartbeats 600000 in
theorem tensorLieAction_realPlace {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v))
    (v : RP) (X : RL) :
    tensorLieAction F n (Vf := Vf) δr δc (realPlaceComplexLieInclusion F n v X) =
      slotAlgebraHom (.inr (.inl v)) (V := SlotSpace F Vf Vr Vc)
        (ULift.moduleEquiv.symm.conjAlgEquiv ℂ (δr v X)) := by
  rw [tensorLieAction, sumSlotLieAction_apply]
  rw [Finset.sum_eq_single (.inr (.inl v))]
  · simp [placeLieAction]; rfl
  · rintro (_ | w | w) _ hw
    · simp [placeLieAction]
    · have hw' : w ≠ v := fun e => hw (congrArg (fun t => Sum.inr (Sum.inl t)) e)
      simp [placeLieAction, realProjection_realPlace, hw']
    · simp [placeLieAction, complexProjection_realPlace]
  · simp

set_option maxHeartbeats 600000 in
theorem tensorLieAction_complexPlace {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v))
    (v : CP) (X : CL) :
    tensorLieAction F n (Vf := Vf) δr δc (complexPlaceComplexLieInclusion F n v X) =
      slotAlgebraHom (.inr (.inr v)) (V := SlotSpace F Vf Vr Vc)
        (ULift.moduleEquiv.symm.conjAlgEquiv ℂ (δc v X)) := by
  rw [tensorLieAction, sumSlotLieAction_apply]
  rw [Finset.sum_eq_single (.inr (.inr v))]
  · simp [placeLieAction]; rfl
  · rintro (_ | w | w) _ hw
    · simp [placeLieAction]
    · simp [placeLieAction, realProjection_complexPlace]
    · have hw' : w ≠ v := fun e => hw (congrArg (fun t => Sum.inr (Sum.inr t)) e)
      simp [placeLieAction, complexProjection_complexPlace, hw']
  · simp

end Actions

private def compactCoordinates : standardInfiniteCompact F n ≃* ArchimedeanCompactFactors F n :=
  (MulEquiv.ofBijective (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
    ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
      ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩).symm

private theorem compactCoordinates_apply (k : ArchimedeanCompactFactors F n) :
    compactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n k) = k :=
  (compactCoordinates F n).apply_symm_apply k

private def compactSlotAction {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v)) (i : Slot F) :
    ArchimedeanCompactFactors F n →* Module.End ℂ (SlotSpace F Vf Vr Vc i) :=
  match i with
  | .inl _ => 1
  | .inr (.inl v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp
      ((κr v).comp <| (Pi.evalMonoidHom (fun _ : RP => RK) v).comp (MonoidHom.fst _ _))
  | .inr (.inr v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp
      ((κc v).comp <| (Pi.evalMonoidHom (fun _ : CP => CK) v).comp (MonoidHom.snd _ _))

private theorem compactSlotAction_real_apply {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v))
    (v : RP) (p : ArchimedeanCompactFactors F n) :
    compactSlotAction F n (Vf := Vf) κr κc (.inr (.inl v)) p =
      ULift.moduleEquiv.symm.conjAlgEquiv ℂ (κr v (p.1 v)) := rfl

private theorem compactSlotAction_complex_apply {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v))
    (v : CP) (p : ArchimedeanCompactFactors F n) :
    compactSlotAction F n (Vf := Vf) κr κc (.inr (.inr v)) p =
      ULift.moduleEquiv.symm.conjAlgEquiv ℂ (κc v (p.2 v)) := rfl

/-- The actual infinite compact acts by the tensor of its place actions. -/
def tensorCompactAction {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v)) :
    Representation ℂ (standardInfiniteCompact F n) (Space F Vf Vr Vc) :=
  PiTensorProduct.mapMonoidHom.comp
    ((MonoidHom.pi (compactSlotAction F n (Vf := Vf) κr κc)).comp
      (compactCoordinates F n).toMonoidHom)

set_option maxHeartbeats 600000 in
theorem tensorCompactAction_realPlace {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v)) (v : RP) (k : RK) :
    tensorCompactAction F n (Vf := Vf) κr κc (realPlaceCompactInclusion F n v k) =
      slotAlgebraHom (.inr (.inl v)) (V := SlotSpace F Vf Vr Vc)
        (ULift.moduleEquiv.symm.conjAlgEquiv ℂ (κr v k)) := by
  change PiTensorProduct.map (fun i => compactSlotAction F n (Vf := Vf) κr κc i
    (compactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v k)))) = PiTensorProduct.map _
  rw [compactCoordinates_apply]
  congr 1
  funext i
  rcases i with _ | w | w
  · simp [compactSlotAction, slot, ← Module.End.one_eq_id]
  · by_cases hw : w = v
    · subst w
      simp [compactSlotAction_real_apply, slot]
    · simp [compactSlotAction_real_apply, slot, hw, ← Module.End.one_eq_id]
  · simp [compactSlotAction_complex_apply, slot, ← Module.End.one_eq_id]

set_option maxHeartbeats 600000 in
theorem tensorCompactAction_complexPlace {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v)) (v : CP) (k : CK) :
    tensorCompactAction F n (Vf := Vf) κr κc (complexPlaceCompactInclusion F n v k) =
      slotAlgebraHom (.inr (.inr v)) (V := SlotSpace F Vf Vr Vc)
        (ULift.moduleEquiv.symm.conjAlgEquiv ℂ (κc v k)) := by
  change PiTensorProduct.map (fun i => compactSlotAction F n (Vf := Vf) κr κc i
    (compactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k)))) = PiTensorProduct.map _
  rw [compactCoordinates_apply]
  congr 1
  funext i
  rcases i with _ | w | w
  · simp [compactSlotAction, slot, ← Module.End.one_eq_id]
  · simp [compactSlotAction_real_apply, slot, ← Module.End.one_eq_id]
  · by_cases hw : w = v
    · subst w
      simp [compactSlotAction_complex_apply, slot]
    · simp [compactSlotAction_complex_apply, slot, hw, ← Module.End.one_eq_id]

variable [NumberField F]

/-- The compact and finite translations and the enveloping action determine
the action of the common free operator algebra. -/
def tensorFreeAction {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (fin : Representation ℂ (FiniteAdelicGL F n) Vf)
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)) :
    FreeOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ (Space F Vf Vr Vc) :=
  FreeAlgebra.lift ℂ <| Sum.elim
    (Sum.elim (fun d => slotAlgebraHom (.inl ()) (V := SlotSpace F Vf Vr Vc) (fin d))
      (tensorCompactAction F n (Vf := Vf) κr κc))
    (UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Vf) δr δc))

set_option maxHeartbeats 900000 in
/-- The constructed free action has the prescribed action at every place. -/
theorem tensorFreeAction_hasActions {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (fin : Representation ℂ (FiniteAdelicGL F n) Vf)
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)) :
    HasActions F n fin κr δr κc δc (tensorFreeAction F n fin κr δr κc δc).toMonoidHom := by
  intro i g
  change tensorFreeAction F n fin κr δr κc δc (FreeAlgebra.ι ℂ (operatorIndex F n i g)) = _
  rw [tensorFreeAction, FreeAlgebra.lift_ι_apply]
  rcases i with ⟨⟨⟩⟩ | v | v
  · rfl
  · rcases g with ⟨k | X⟩
    · exact tensorCompactAction_realPlace F n (Vf := Vf) κr κc v k
    · change UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Vf) δr δc)
        (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) = _
      rw [envelopingGenerator, UniversalEnvelopingAlgebra.lift_ι_apply]
      exact tensorLieAction_realPlace F n (Vf := Vf) δr δc v X
  · rcases g with ⟨k | X⟩
    · exact tensorCompactAction_complexPlace F n (Vf := Vf) κr κc v k
    · change UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Vf) δr δc)
        (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) = _
      rw [envelopingGenerator, UniversalEnvelopingAlgebra.lift_ι_apply]
      exact tensorLieAction_complexPlace F n (Vf := Vf) δr δc v X

end Langlands.Global.AdelicOperatorTensor
