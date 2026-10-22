import Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeStatement
import Langlands.ClassFieldTheory.Local.FixedFieldStages
import Langlands.Galois.Local.UnramifiedCriterionProof

/-! # Finite unramified stages under a specified closure embedding -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open Langlands.LocalClassField Langlands.Weil.Local

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Finite unramified Galois stages remain contained in finite unramified
Galois stages after finite base extension, for the specified closure map. -/
theorem unramifiedBaseChangeStageExistence : UnramifiedBaseChangeStageExistence.{u} := by
  intro p _ F E _ _ _ _ _ L _ hL
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : CharZero E.Carrier := Algebra.charZero_of_charZero (Padic p) E.Carrier
  let f : F.Carrier →ₐ[Padic p] E.Carrier :=
    IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier
  let j := extensionGaloisMap F E f
  let N : OpenNormalSubgroup (Field.absoluteGaloisGroup E.Carrier) :=
    { toSubgroup := L.field.fixingSubgroup.comap j.toMonoidHom
      isOpen' := (IntermediateField.fixingSubgroup_isOpen L.field).preimage j.continuous
      isNormal' := (IsGalois.fixingSubgroup_normal_of_isGalois L.field).comap
        j.toMonoidHom }
  let M : FiniteIntermediateExtension E.Carrier :=
    ⟨finiteStageFixedField E.Carrier N, finiteStageFixedField_finiteDimensional E.Carrier N⟩
  have : IsGalois E.Carrier M.field := finiteStageFixedField_isGalois E.Carrier N
  have hfix : M.field.fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField (finiteStageClosedSubgroup E.Carrier N)
  have hLI := (Langlands.PadicField.canonicalUnramifiedCriterion p F L).mp hL
  refine ⟨M, inferInstance, ?_, ?_⟩
  · apply (Langlands.PadicField.canonicalUnramifiedCriterion p E M).mpr
    rw [hfix]
    intro σ hσ
    apply hLI
    rw [← F.absoluteResidueHom_ker F.canonicalTopologicalData]
    change localResidueMap F (extensionGaloisMap F E f σ) = 1
    rw [localResidueMap_extensionGaloisMap]
    have hσ' : localResidueMap E σ = 1 := by
      rw [← E.absoluteResidueHom_ker E.canonicalTopologicalData] at hσ
      exact hσ
    rw [hσ', map_one]
  · intro a
    let e := extensionClosureEquiv F E f
    let c : AlgebraicClosure F.Carrier →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
      { toRingHom := e.symm.toRingHom.comp
          (algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier))
        commutes' := by
          intro x
          apply e.injective
          change e (e.symm (algebraMap (AlgebraicClosure F.Carrier)
            (AlgebraicClosure E.Carrier)
              (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x))) =
                e (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x)
          rw [e.apply_symm_apply]
          change algebraMap (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)
              (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x) =
            extensionClosureLift F E f (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x)
          rw [extensionClosureLift_algebraMap]
          exact (IsScalarTower.algebraMap_apply F.Carrier
            (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier) x).symm.trans
              (IsScalarTower.algebraMap_apply F.Carrier E.Carrier
                (AlgebraicClosure E.Carrier) x) }
    let g := c.comp L.field.val
    have hg : g a ∈ L.field := by
      exact (AlgHom.fieldRange_of_normal g).le (AlgHom.mem_fieldRange.mpr ⟨a, rfl⟩)
    change _ ∈ IntermediateField.fixedField N.toSubgroup
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hga : AlgEquiv.toAlgHom (extensionGaloisMap F E f σ) (g a) = g a :=
      (IntermediateField.mem_fixingSubgroup_iff L.field _).mp hσ (g a) hg
    have he : e (g a) = algebraMap (AlgebraicClosure F.Carrier)
        (AlgebraicClosure E.Carrier) (algebraMap L.field (AlgebraicClosure F.Carrier) a) :=
      e.apply_symm_apply _
    rw [← he]
    exact (extensionClosureLift_galoisMap F E f σ (g a)).symm.trans (congrArg e hga)

end Langlands.ClassFieldTheory.Local
