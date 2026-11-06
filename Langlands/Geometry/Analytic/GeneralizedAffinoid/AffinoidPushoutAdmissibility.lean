import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidCompletedTensor
import Langlands.Geometry.Analytic.AdmissibleEpimorphism

/-! # Admissible quotient maps from the genuine completed tensor to an affinoid pushout -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [Algebra K A]
  {B : Type w} [NormedCommRing B] [Algebra K B]
  {C : Type z} [NormedCommRing C] [Algebra K C]
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K C A)

/-- A bounded factor of a map with controlled lifts also has controlled lifts. -/
theorem IsAdmissibleEpi.of_comp (h : (f.comp g).IsAdmissibleEpi) :
    f.IsAdmissibleEpi := by
  obtain ⟨M, hM, hlifts⟩ := (f.comp g).isAdmissibleEpi_iff_normControlledLifts.mp h
  obtain ⟨N, hN, hbound⟩ := g.bounded
  apply f.isAdmissibleEpi_iff_normControlledLifts.mpr
  refine ⟨N * M, mul_pos hN hM, fun b => ?_⟩
  obtain ⟨c, hc, hnorm⟩ := hlifts b
  refine ⟨g c, hc, ?_⟩
  exact (hbound c).trans
    ((mul_le_mul_of_nonneg_left hnorm hN.le).trans_eq (mul_assoc _ _ _).symm)

end Langlands.Analytic.BoundedAlgHom

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

/-- The actual map from the absolute affinoid coproduct to the relative pushout. -/
def coproductMap :
    BoundedAlgHom K (AffinoidCoproduct.algebra K B C) (algebra f g) :=
  AffinoidCoproduct.lift K (algebra f g) B C (leftMap f g) (rightMap f g)

@[simp]
theorem coproductMap_comp_leftMap :
    (coproductMap f g).comp (AffinoidCoproduct.leftMap K B C) = leftMap f g :=
  AffinoidCoproduct.lift_comp_leftMap K (algebra f g) B C _ _

@[simp]
theorem coproductMap_comp_rightMap :
    (coproductMap f g).comp (AffinoidCoproduct.rightMap K B C) = rightMap f g :=
  AffinoidCoproduct.lift_comp_rightMap K (algebra f g) B C _ _

/-- Both quotients use the same appended weighted Tate variables. -/
theorem coproductMap_comp_presentationMap :
    (coproductMap f g).comp
        (presentationMap K (AffinoidCoproduct.algebra K B C)) =
      presentationMap K (algebra f g) := by
  apply GeneralizedTateAlgebra.hom_ext
  intro i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · change coproductMap f g
      (coordinate K (AffinoidCoproduct.algebra K B C) (Fin.castAdd C.arity k)) =
        coordinate K (algebra f g) (Fin.castAdd C.arity k)
    exact (congrArg (coproductMap f g) (leftMap_coordinate (B := B) (C := C)
      (AffinoidCoproduct.initialMap K B) (AffinoidCoproduct.initialMap K C) k)).symm.trans
      ((congrArg (fun h : BoundedAlgHom K B (algebra f g) => h (coordinate K B k))
        (coproductMap_comp_leftMap f g)).trans (leftMap_coordinate f g k))
  · change coproductMap f g
      (coordinate K (AffinoidCoproduct.algebra K B C) (Fin.natAdd B.arity k)) =
        coordinate K (algebra f g) (Fin.natAdd B.arity k)
    exact (congrArg (coproductMap f g) (rightMap_coordinate (B := B) (C := C)
      (AffinoidCoproduct.initialMap K B) (AffinoidCoproduct.initialMap K C) k)).symm.trans
      ((congrArg (fun h : BoundedAlgHom K C (algebra f g) => h (coordinate K C k))
        (coproductMap_comp_rightMap f g)).trans (rightMap_coordinate f g k))

/-- The pushout map is admissible by the actual target quotient's small lifts. -/
theorem coproductMap_isAdmissibleEpi : (coproductMap f g).IsAdmissibleEpi := by
  apply BoundedAlgHom.IsAdmissibleEpi.of_comp (coproductMap f g)
    (presentationMap K (AffinoidCoproduct.algebra K B C))
  rw [coproductMap_comp_presentationMap]
  exact presentationMap_isAdmissibleEpi K (algebra f g)

/-- The genuine projective completed-tensor quotient onto the relative pushout. -/
def tensorMap :
    BoundedAlgHom K (CompletedTensorAlgebra.Algebra K B C) (algebra f g) :=
  CompletedTensorAlgebra.lift (leftMap f g) (rightMap f g)

@[simp]
theorem tensorMap_comp_leftMap :
    (tensorMap f g).comp (CompletedTensorAlgebra.leftMap K B C) = leftMap f g :=
  CompletedTensorAlgebra.lift_comp_leftMap _ _

@[simp]
theorem tensorMap_comp_rightMap :
    (tensorMap f g).comp (CompletedTensorAlgebra.rightMap K B C) = rightMap f g :=
  CompletedTensorAlgebra.lift_comp_rightMap _ _

/-- The finite-presentation quotient and genuine completed-tensor map agree. -/
theorem coproductMap_comp_fromCompletedTensor :
    (coproductMap f g).comp (AffinoidCoproduct.fromCompletedTensor K B C) =
      tensorMap f g :=
  AffinoidCoproduct.lift_comp_fromCompletedTensor K B C _ _

/-- No open mapping theorem is used: both surjectivity and uniform quotient-norm
comparison follow from quotient lifts and the constructed bounded comparison. -/
theorem tensorMap_isAdmissibleEpi : (tensorMap f g).IsAdmissibleEpi := by
  rw [← coproductMap_comp_fromCompletedTensor]
  apply BoundedAlgHom.IsAdmissibleEpi.comp
    (AffinoidCoproduct.fromCompletedTensor K B C) (coproductMap f g)
  · exact BoundedAlgHom.isAdmissibleEpi_of_bounded_section _
      (AffinoidCoproduct.toCompletedTensor K B C)
      (AffinoidCoproduct.fromCompletedTensor_comp_toCompletedTensor K B C)
  · exact coproductMap_isAdmissibleEpi f g

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
