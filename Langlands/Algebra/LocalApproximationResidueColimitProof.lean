import Langlands.Algebra.LocalApproximationResidueColimitStatement
import Langlands.Algebra.LocalApproximationResidueModuleColimit
import Langlands.Algebra.LocalModuleApproximation
import Langlands.Algebra.RingAdditiveColimit

/-! # Preservation of the actual local residue-fibre colimits -/

open scoped TensorProduct
open IsLocalRing
open scoped Langlands.Algebra.LocalModuleSystem
open scoped Langlands.Algebra.ResidueFiberTensor

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra
namespace ResidueColimitProof

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- Every target residue class comes from a component if the base colimit is onto. -/
theorem exists_residueι_eq (hR : Function.Surjective D.baseColimitMap)
    (a : ResidueField R) : ∃ i, ∃ b : ResidueField (D.base i), D.residueι i b = a := by
  obtain ⟨r, rfl⟩ := residue_surjective a
  obtain ⟨i, r', rfl⟩ := D.exists_baseι_eq hR r
  exact ⟨i, residue (D.base i) r', D.residueι_residue i r'⟩

/-- The actual lift from the residue-field diagram is bijective. -/
theorem residueLift_bijective (hR : Function.Bijective D.baseColimitMap) :
    Function.Bijective
      (Ring.DirectLimit.lift (fun i ↦ ResidueField (D.base i))
        (fun _ _ h ↦ D.residueMap h) (ResidueField R) (fun i ↦ D.residueι i)
        (fun _ _ h a ↦ D.residueι_compat h a)) := by
  constructor
  · apply Ring.DirectLimit.lift_injective
    intro i
    exact (D.residueι i).injective
  · intro a
    obtain ⟨i, b, rfl⟩ := exists_residueι_eq D hR.2 a
    exact ⟨Ring.DirectLimit.of _ _ i b, by simp⟩

/-- Switching tensor factors identifies each fibre ring additively with the regular
module's residue fibre. -/
noncomputable def regularFiberEquiv (i : ι) :
    D.FiberRing i ≃+ D.regularModuleSystem.ResidueFiber i :=
  (TensorProduct.rid (D.alg i) (D.FiberRing i)).symm.toAddEquiv.trans
    (D.regularModuleSystem.fiberModuleEquiv i).toAddEquiv

/-- A pure tensor with the regular module's specified restricted base action. -/
noncomputable def regularTmul (i : ι) (a : ResidueField (D.base i)) (s : D.alg i) :
    D.regularModuleSystem.ResidueFiber i := by
  letI := D.regularModuleSystem.objBaseModule i
  exact a ⊗ₜ[D.base i] s

@[simp] theorem regularFiberEquiv_tmul (i : ι) (s : D.alg i)
    (a : ResidueField (D.base i)) :
    regularFiberEquiv D i (s ⊗ₜ[D.base i] a) = regularTmul D i a s := by
  change regularTmul D i a (s * 1) = _
  rw [mul_one]

/-- The corresponding target comparison. -/
noncomputable def regularTargetEquiv :
    LocalAlgebraSystem.TargetFiberRing R S ≃+
      LocalModuleSystem.TargetResidueFiber R S :=
  (TensorProduct.comm R S (ResidueField R)).toAddEquiv

@[simp] theorem regularFiberEquiv_map {i j : ι} (h : i ≤ j) (x : D.FiberRing i) :
    regularFiberEquiv D j (D.fiberRingMap h x) =
      D.regularModuleSystem.residueFiberMap h (regularFiberEquiv D i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    simp only [LocalAlgebraSystem.fiberRingMap_tmul, regularFiberEquiv_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

@[simp] theorem regularTargetEquiv_ι (i : ι) (x : D.FiberRing i) :
    regularTargetEquiv (R := R) (S := S) (D.fiberRingι i x) =
      D.regularModuleSystem.residueFiberι i (regularFiberEquiv D i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    simp only [LocalAlgebraSystem.fiberRingι_tmul, regularFiberEquiv_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- Bijectivity for the actual regular-module lift implies bijectivity for the
actual fibre-ring lift. -/
theorem fiberRingLift_bijective_of_regular
    (h : letI := Classical.decEq ι
      Function.Bijective
        (AddCommGroup.DirectLimit.lift D.regularModuleSystem.ResidueFiber
          (fun _ _ h ↦ (D.regularModuleSystem.residueFiberMap h).toAddMonoidHom)
          (LocalModuleSystem.TargetResidueFiber R S)
          (fun i ↦ (D.regularModuleSystem.residueFiberι i).toAddMonoidHom)
          (fun _ _ h x ↦ D.regularModuleSystem.residueFiberι_compat h x))) :
    Function.Bijective
      (Ring.DirectLimit.lift D.FiberRing (fun _ _ h ↦ D.fiberRingMap h)
        (LocalAlgebraSystem.TargetFiberRing R S) (fun i ↦ D.fiberRingι i)
        (fun _ _ h x ↦ D.fiberRingι_compat h x)) := by
  classical
  have : DirectedSystem D.regularModuleSystem.ResidueFiber
      (fun {_ _} h ↦ (D.regularModuleSystem.residueFiberMap h).toAddMonoidHom) :=
    { map_self := fun {_} ↦ D.regularModuleSystem.residueFiberMap_self _
      map_map := fun {_ _ _} ↦ D.regularModuleSystem.residueFiberMap_comp }
  let L := AddCommGroup.DirectLimit.lift D.regularModuleSystem.ResidueFiber
    (fun _ _ h ↦ (D.regularModuleSystem.residueFiberMap h).toAddMonoidHom)
    (LocalModuleSystem.TargetResidueFiber R S)
    (fun i ↦ (D.regularModuleSystem.residueFiberι i).toAddMonoidHom)
    (fun _ _ h x ↦ D.regularModuleSystem.residueFiberι_compat h x)
  let F := Ring.DirectLimit.lift D.FiberRing (fun _ _ h ↦ D.fiberRingMap h)
    (LocalAlgebraSystem.TargetFiberRing R S) (fun i ↦ D.fiberRingι i)
    (fun _ _ h x ↦ D.fiberRingι_compat h x)
  have L_of (i : ι) (a : D.regularModuleSystem.ResidueFiber i) :
      L (AddCommGroup.DirectLimit.of D.regularModuleSystem.ResidueFiber
        (fun _ _ h ↦ (D.regularModuleSystem.residueFiberMap h).toAddMonoidHom) i a) =
        D.regularModuleSystem.residueFiberι i a := by
    exact AddCommGroup.DirectLimit.lift_of _ _ _ i a
  change Function.Bijective L at h
  change Function.Bijective F
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
    have hx : D.fiberRingι i x = 0 := by
      simpa only [F, Ring.DirectLimit.lift_of] using hz
    have ha : AddCommGroup.DirectLimit.of D.regularModuleSystem.ResidueFiber
        (fun _ _ h ↦ (D.regularModuleSystem.residueFiberMap h).toAddMonoidHom) i
        (regularFiberEquiv D i x) = 0 := by
      apply h.1
      rw [L_of, map_zero]
      simpa only [map_zero, regularTargetEquiv_ι]
        using congrArg (regularTargetEquiv (R := R) (S := S)) hx
    obtain ⟨j, hij, haj⟩ := AddCommGroup.DirectLimit.of.zero_exact _ _ ha
    have hxj : D.fiberRingMap hij x = 0 := by
      apply (regularFiberEquiv D j).injective
      simpa only [regularFiberEquiv_map, map_zero, LinearMap.toAddMonoidHom_coe] using haj
    rw [← Ring.DirectLimit.of_f hij x, hxj, map_zero]
  · intro y
    obtain ⟨z, hz⟩ := h.2 (regularTargetEquiv (R := R) (S := S) y)
    induction z using AddCommGroup.DirectLimit.induction_on with
    | ih i a =>
      rw [L_of] at hz
      refine ⟨Ring.DirectLimit.of D.FiberRing (fun _ _ h ↦ D.fiberRingMap h) i
        ((regularFiberEquiv D i).symm a), ?_⟩
      apply (regularTargetEquiv (R := R) (S := S)).injective
      simpa only [F, Ring.DirectLimit.lift_of, regularTargetEquiv_ι,
        AddEquiv.apply_symm_apply] using hz

/-- The actual fibre-ring lift is bijective when the original ring cocones are colimits. -/
theorem fiberRingLift_bijective (hD : D.IsColimit) :
    Function.Bijective
      (Ring.DirectLimit.lift D.FiberRing (fun _ _ h ↦ D.fiberRingMap h)
        (LocalAlgebraSystem.TargetFiberRing R S) (fun i ↦ D.fiberRingι i)
        (fun _ _ h x ↦ D.fiberRingι_compat h x)) := by
  apply fiberRingLift_bijective_of_regular D
  exact localApproximationResidueModuleColimit ι R S D S D.regularModuleSystem
    (D.regularModuleSystem_isColimit hD)

end ResidueColimitProof

open ResidueColimitProof in
/-- Preservation of the actual residue-field, fibre-ring and residue-module colimits. -/
theorem localApproximationResidueColimit :
    LocalApproximationResidueColimitStatement.{uI, uA, uB, uN, uR, uS, uM} := by
  intro ι _ _ _ R S _ _ _ _ _ _ D
  refine ⟨residueLift_bijective D, fiberRingLift_bijective D, ?_⟩
  intro M _ _ _ _ E hE
  exact localApproximationResidueModuleColimit ι R S D M E hE

end Langlands.Algebra
