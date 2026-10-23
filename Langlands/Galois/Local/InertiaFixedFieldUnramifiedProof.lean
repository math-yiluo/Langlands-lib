import Langlands.Galois.Local.InertiaFixedFieldUnramifiedStatement
import Langlands.Galois.Local.UnramifiedCriterionProof
import Mathlib.FieldTheory.Normal.Closure

/-! # Finite unramified exhaustion of the actual inertia fixed field -/

namespace Langlands.PadicField

universe u

/-- Every finite subset of the actual inertia fixed field lies in a finite
unramified Galois intermediate extension, and every such extension is fixed. -/
theorem inertiaFixedFieldUnramifiedExhaustion :
    InertiaFixedFieldUnramifiedExhaustion.{u} := by
  intro p _ F
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
  have : IsGalois F.Carrier U :=
    @IsGalois.of_fixedField_normal_subgroup F.Carrier (AlgebraicClosure F.Carrier)
      _ _ _ inferInstance (F.absoluteInertia F.canonicalTopologicalData)
      (F.absoluteInertia_normal F.canonicalTopologicalData)
  constructor
  · intro E _ hE
    exact (IntermediateField.le_iff_le _ _).mpr ((canonicalUnramifiedCriterion p F E).mp hE)
  · intro s hs
    let A := IntermediateField.adjoin F.Carrier (s : Set (AlgebraicClosure F.Carrier))
    have : FiniteDimensional F.Carrier A :=
      IntermediateField.finiteDimensional_adjoin fun x _ =>
        Algebra.IsIntegral.isIntegral (R := F.Carrier) x
    let L := IntermediateField.normalClosure F.Carrier A (AlgebraicClosure F.Carrier)
    have hAU : A ≤ U := IntermediateField.adjoin_le_iff.mpr hs
    have hLU : L ≤ U := IntermediateField.normalClosure_le_iff_of_normal.mpr hAU
    let E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier :=
      ⟨L, inferInstance⟩
    have : IsGalois F.Carrier E.field := IsGalois.normalClosure _ _ _
    refine ⟨E, inferInstance, ?_, ?_⟩
    · exact (canonicalUnramifiedCriterion p F E).mpr
        ((IntermediateField.le_iff_le _ _).mp hLU)
    · intro x hx
      exact IntermediateField.le_normalClosure A
        (IntermediateField.subset_adjoin F.Carrier _ hx)

end Langlands.PadicField
