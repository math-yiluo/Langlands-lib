import Langlands.Automorphic.UnitaryContragredientCriterion
import Langlands.Global.AdelicOperatorTensorAction
import Langlands.Representation.RestrictedTensor.PointwiseEvaluation

/-! # Joint admissibility of an adelic tensor from separating compact evaluations -/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global.AdelicOperatorTensor

open NumberField Langlands.FiniteTensor Langlands.RestrictedTensor Langlands.Automorphic

private theorem tensor_evaluations_separate {I : Type*} [Fintype I]
    {X V W : I → Type*} [∀ i, Nonempty (X i)]
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ev : ∀ i, X i → V i →ₗ[ℂ] W i)
    (hsep : ∀ i (f : V i), (∀ p, ev i p f = 0) → f = 0)
    (x : ⨂[ℂ] i, V i) (hx : ∀ p : ∀ i, X i, PiTensorProduct.map (fun i => ev i (p i)) x = 0) :
    x = 0 := by
  let E : Finset I := Finset.univ
  let S : Index E := ⟨E, le_rfl⟩
  let reindex : E ≃ I := Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective, fun i => ⟨⟨i, Finset.mem_univ i⟩, rfl⟩⟩
  let a (i : I) : V i := 0
  let b (i : I) : W i := 0
  have ha (i : I) (hi : i ∉ E) : a i ≠ 0 := (hi (Finset.mem_univ i)).elim
  have hb (i : I) (hi : i ∉ E) : b i ≠ 0 := (hi (Finset.mem_univ i)).elim
  have hr (i : I) (_hi : i ∉ E) (p : X i) : ev i p (a i) = b i := map_zero _
  let j := (of ℂ V E a S).comp (PiTensorProduct.reindex ℂ V reindex.symm).toLinearMap
  have hj : Function.Injective j :=
    (of_injective E a ha S).comp (PiTensorProduct.reindex ℂ V reindex.symm).injective
  apply (injective_iff_map_eq_zero j).mp hj
  apply (injective_iff_map_eq_zero _).mp (pointwiseEvaluation_injective ev E a b hr hsep hb)
  funext p
  change pointwiseEvaluation ev E a b hr (of ℂ V E a S
    (PiTensorProduct.reindex ℂ V reindex.symm x)) p = 0
  rw [pointwiseEvaluation_of]
  have h := PiTensorProduct.map_reindex (fun i => ev i (p i)) reindex.symm x
  rw [hx, map_zero] at h
  exact (congrArg (of ℂ W E b S) h).trans (map_zero _)

private theorem jointlyAdmissible_of_evaluation {G K V W : Type*} [Group G] [Group K]
    [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {κ : Representation ℂ K V} {fin : Representation ℂ G W}
    (e : V →ₗ[ℂ] W) (he : ∀ g x, e (ρ g x) = fin g (e x))
    (hsep : ∀ x, (∀ k, e (κ k x) = 0) → x = 0) (hadm : IsAdmissible fin) :
    IsJointlyAdmissible ρ κ := by
  intro L d τ
  let M := jointMultiplicitySpace ρ κ L.toSubgroup τ
  let D := fixedVectors fin L.toSubgroup
  let : Module.Finite ℂ D := hadm.2 L
  let P : M →ₗ[ℂ] ((Fin d → ℂ) →ₗ[ℂ] D) :=
    { toFun := fun f => (e.comp f.val).codRestrict D (fun y g => by
        change fin g.val (e (f.val y)) = e (f.val y)
        rw [← he]
        exact congrArg e (f.property.1 y g))
      map_add' := fun f g => LinearMap.ext fun y => Subtype.ext (e.map_add (f.val y) (g.val y))
      map_smul' := fun c f => LinearMap.ext fun y => Subtype.ext (e.map_smul c (f.val y)) }
  apply Module.Finite.of_injective P
  apply (injective_iff_map_eq_zero P).mpr
  intro f hf
  apply Subtype.ext
  apply LinearMap.ext
  intro y
  change f.val y = 0
  apply hsep (f.val y)
  intro k
  rw [← f.property.2]
  exact congrArg (fun q : (Fin d → ℂ) →ₗ[ℂ] D => (q (τ k y)).val) hf

universe u

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ

variable {Vf : Type u}
  {Vr : {v : InfinitePlace F // InfinitePlace.IsReal v} → Type}
  {Vc : {v : InfinitePlace F // InfinitePlace.IsComplex v} → Type}
  [AddCommGroup Vf] [Module ℂ Vf]
  [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
  [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]

/-- Finite translations operate on the grouped finite tensor slot. -/
def tensorFiniteAction (fin : Representation ℂ (FiniteAdelicGL F n) Vf) :
    Representation ℂ (FiniteAdelicGL F n) (AdelicOperatorTensor.Space F Vf Vr Vc) := by
  exact (slotAlgebraHom (k := ℂ) (.inl ()) (V := SlotSpace F Vf Vr Vc)).toMonoidHom.comp fin

private abbrev ScalarSlots := SlotSpace F Vf (fun _ => ℂ) (fun _ => ℂ)

private def unliftScalar (i : RP ⊕ CP) : ScalarSlots F (Vf := Vf) (.inr i) ≃ₗ[ℂ] ℂ :=
  match i with
  | .inl _ => ULift.moduleEquiv
  | .inr _ => ULift.moduleEquiv

private def tensorScalarCollapse : (⨂[ℂ] i, ScalarSlots F (Vf := Vf) i) ≃ₗ[ℂ] Vf :=
  (PiTensorProduct.tmulEquivDep ℂ (ScalarSlots F (Vf := Vf))).symm.trans <|
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv (R := ℂ) ())
      ((PiTensorProduct.congr (unliftScalar F)).trans
        (PiTensorProduct.constantBaseRingEquiv (RP ⊕ CP) ℂ).toLinearEquiv)).trans
      (TensorProduct.rid ℂ Vf)

private theorem tensorScalarCollapse_tprod (x : ∀ i, ScalarSlots F (Vf := Vf) i) :
    tensorScalarCollapse F (PiTensorProduct.tprod ℂ x) =
      (∏ i : RP ⊕ CP, unliftScalar F i (x (.inr i))) • x (.inl ()) := by
  simp [tensorScalarCollapse]
  rfl

private def Test : Slot F → Type u
  | .inl _ => PUnit
  | .inr (.inl _) => ULift.{u} RK
  | .inr (.inr _) => ULift.{u} CK

private instance testNonempty (i : Slot F) : Nonempty (Test F n i) :=
  match i with
  | .inl _ => ⟨PUnit.unit⟩
  | .inr (.inl _) => ⟨⟨1⟩⟩
  | .inr (.inr _) => ⟨⟨1⟩⟩

variable (κr : ∀ v, Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (Vr v))
  (κc : ∀ v, Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (Vc v))
  (er : ∀ v, Vr v →ₗ[ℂ] ℂ) (ec : ∀ v, Vc v →ₗ[ℂ] ℂ)

private def slotEvaluation (i : Slot F) :
    Test F n i → SlotSpace F Vf Vr Vc i →ₗ[ℂ] ScalarSlots F (Vf := Vf) i :=
  match i with
  | .inl _ => fun _ => LinearMap.id
  | .inr (.inl v) => fun p => ULift.moduleEquiv.symm.toLinearMap.comp
      ((er v).comp ((κr v p.down).comp ULift.moduleEquiv.toLinearMap))
  | .inr (.inr v) => fun p => ULift.moduleEquiv.symm.toLinearMap.comp
      ((ec v).comp ((κc v p.down).comp ULift.moduleEquiv.toLinearMap))

private def coordinates (p : ∀ i, Test F n i) : ArchimedeanCompactFactors F n :=
  (fun v => (p (.inr (.inl v))).down, fun v => (p (.inr (.inr v))).down)

private def unitTest (i : Slot F) : Test F n i :=
  match i with
  | .inl _ => PUnit.unit
  | .inr (.inl _) => ⟨1⟩
  | .inr (.inr _) => ⟨1⟩

/-- Evaluate the archimedean factors at the identity, retaining the finite slot. -/
def tensorCompactEvaluation : AdelicOperatorTensor.Space F Vf Vr Vc →ₗ[ℂ] Vf :=
  (tensorScalarCollapse F).toLinearMap.comp
    (PiTensorProduct.map (fun i => slotEvaluation F n κr κc er ec i (unitTest F n i)))

private theorem tensorCompactEvaluation_finite
    (fin : Representation ℂ (FiniteAdelicGL F n) Vf) (g : FiniteAdelicGL F n)
    (x : AdelicOperatorTensor.Space F Vf Vr Vc) :
    tensorCompactEvaluation F n κr κc er ec (tensorFiniteAction F n fin g x) =
      fin g (tensorCompactEvaluation F n κr κc er ec x) := by
  have hmap : (tensorCompactEvaluation F n κr κc er ec).comp (tensorFiniteAction F n fin g) =
      (fin g).comp (tensorCompactEvaluation F n κr κc er ec) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    change tensorCompactEvaluation F n κr κc er ec
      (PiTensorProduct.map (slot (.inl ()) (fin g)) (PiTensorProduct.tprod ℂ w)) = _
    simp only [PiTensorProduct.map_tprod, tensorCompactEvaluation, LinearMap.comp_apply,
      LinearEquiv.coe_coe, tensorScalarCollapse_tprod]
    have htail (i : RP ⊕ CP) :
        slot (V := SlotSpace F Vf Vr Vc) (.inl ()) (fin g) (.inr i) (w (.inr i)) = w (.inr i) := by
      simp [slot]
    simp only [htail]
    simp [slotEvaluation, unitTest, slot, map_smul]
    rfl
  exact LinearMap.congr_fun hmap x

set_option maxHeartbeats 1500000 in
private theorem tensorCompactEvaluation_compact (p : ∀ i, Test F n i) (x : AdelicOperatorTensor.Space F Vf Vr Vc) :
    tensorCompactEvaluation F n κr κc er ec
      (tensorCompactAction F n κr κc (ArchimedeanCompactFactors.toStandardCompact F n (coordinates F n p)) x) =
      tensorScalarCollapse F (PiTensorProduct.map (fun i => slotEvaluation F n κr κc er ec i (p i)) x) := by
  let j := ArchimedeanCompactFactors.toStandardCompact F n
  let c := MulEquiv.ofBijective j.toMonoidHom
    ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
      ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩
  let q := coordinates F n p
  have hc : c.symm (j q) = q := c.symm_apply_apply q
  let a (i : Slot F) : ArchimedeanCompactFactors F n →* Module.End ℂ (SlotSpace F Vf Vr Vc i) :=
    match i with
    | .inl _ => 1
    | .inr (.inl v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp
        ((κr v).comp ((Pi.evalMonoidHom (fun _ : RP => RK) v).comp (MonoidHom.fst _ _)))
    | .inr (.inr v) => (ULift.moduleEquiv.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp
        ((κc v).comp ((Pi.evalMonoidHom (fun _ : CP => CK) v).comp (MonoidHom.snd _ _)))
  have ha : tensorCompactAction F n (Vf := Vf) κr κc (j q) =
      PiTensorProduct.map (fun i => a i q) := by
    change PiTensorProduct.map (fun i => a i (c.symm (j q))) = _
    rw [hc]
  have hmap : (tensorCompactEvaluation F n κr κc er ec).comp (tensorCompactAction F n κr κc (j q)) =
      (tensorScalarCollapse F (Vf := Vf)).toLinearMap.comp
        (PiTensorProduct.map (fun i => slotEvaluation F n κr κc er ec i (p i))) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [ha]
    simp only [PiTensorProduct.map_tprod, tensorCompactEvaluation, LinearMap.comp_apply, LinearEquiv.coe_coe]
    congr 2
    funext i
    rcases i with (_ | v | v)
    · rfl
    · change (ULift.up (er v ((κr v 1) ((κr v (q.1 v)) (w (.inr (.inl v))).down)))) = _
      simp only [map_one, Module.End.one_apply]
      rfl
    · change (ULift.up (ec v ((κc v 1) ((κc v (q.2 v)) (w (.inr (.inr v))).down)))) = _
      simp only [map_one, Module.End.one_apply]
      rfl
  exact LinearMap.congr_fun hmap x

set_option maxHeartbeats 1700000 in
/-- Finite admissibility and separating compact evaluations on each
archimedean factor imply joint admissibility for the full action. -/
theorem tensor_isJointlyAdmissible (fin : Representation ℂ (FiniteAdelicGL F n) Vf)
    (hadm : IsAdmissible fin)
    (hr : ∀ v x, (∀ k, er v (κr v k x) = 0) → x = 0)
    (hc : ∀ v x, (∀ k, ec v (κc v k x) = 0) → x = 0) :
    IsJointlyAdmissible (tensorFiniteAction F n fin) (tensorCompactAction F n κr κc) := by
  refine jointlyAdmissible_of_evaluation (tensorCompactEvaluation F n κr κc er ec)
    (tensorCompactEvaluation_finite F n κr κc er ec fin) ?_ hadm
  intro x hx
  refine tensor_evaluations_separate (slotEvaluation F n κr κc er ec) ?_ x (fun p => ?_)
  · rintro (i | v | v) y hy
    · exact hy PUnit.unit
    · apply ULift.ext
      exact hr v y.down fun k => congrArg ULift.down (hy ⟨k⟩)
    · apply ULift.ext
      exact hc v y.down fun k => congrArg ULift.down (hy ⟨k⟩)
  · apply (injective_iff_map_eq_zero _).mp (tensorScalarCollapse F).injective
    rw [← tensorCompactEvaluation_compact F n κr κc er ec p]
    exact hx _

end Langlands.Global.AdelicOperatorTensor
