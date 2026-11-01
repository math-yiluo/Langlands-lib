import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentGluingStatement
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentTrivialScalar
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentDiagramComparisonProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentGluingProof

/-! # Scalar descent for the actual strict binary Laurent diagram -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Compatible scalar sections of the actual strict binary Laurent quotients
come from a unique element of the presented strict base, over every complete
ultrametric normed field. -/
theorem binaryLaurentGluing : BinaryLaurentGluingStatement.{u} := by
  intro K _ _ _ P f sUpper sLower hcompat
  by_cases hK : ∀ c : K, ‖c‖ ≤ 1
  · exact binaryLaurentGluing_of_trivialScalar hK f sUpper sLower hcompat
  · have hnontrivial : ∃ c : K, 1 < ‖c‖ := by
      simpa only [not_forall, not_le] using hK
    let A := PresentedAffinoidAlgebra.ofStrict K P
    let e := PresentedAffinoidAlgebra.strictEquiv K P
    let fRel : A := e.symm f
    obtain ⟨eUpper, eLower, eOverlap, hUpper, hLower, _, hLeft, hRight⟩ :=
      binaryLaurentDiagramComparison K P f
    have hrel :
        PresentedAffinoidAlgebra.BinaryLaurent.left K A fRel (eUpper sUpper) =
          PresentedAffinoidAlgebra.BinaryLaurent.right K A fRel (eLower sLower) :=
      (hLeft sUpper).symm.trans ((congrArg eOverlap hcompat).trans (hRight sLower))
    obtain ⟨a, ha, hunique⟩ :=
      PresentedAffinoidAlgebra.BinaryLaurent.gluing K hnontrivial P fRel
        (eUpper sUpper) (eLower sLower) hrel
    refine ⟨e a, ⟨?_, ?_⟩, ?_⟩
    · apply eUpper.toAlgEquiv.injective
      rw [hUpper]
      simpa only [e, BoundedAlgEquiv.symm_apply_apply] using ha.1
    · apply eLower.toAlgEquiv.injective
      rw [hLower]
      simpa only [e, BoundedAlgEquiv.symm_apply_apply] using ha.2
    · intro b hb
      have hba : e.symm b = a := hunique (e.symm b)
        ⟨(hUpper b).symm.trans (congrArg eUpper hb.1),
          (hLower b).symm.trans (congrArg eLower hb.2)⟩
      apply e.symm.toAlgEquiv.injective
      simpa only [BoundedAlgEquiv.symm_apply_apply] using hba

end Langlands.Analytic.StrictTestDomain
