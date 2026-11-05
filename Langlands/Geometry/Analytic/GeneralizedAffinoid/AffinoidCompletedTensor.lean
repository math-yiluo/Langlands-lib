import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidCoproduct
import Langlands.Geometry.Analytic.CompletedTensorUniversal

/-! # Actual affinoid presentation of the completed tensor algebra -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidCoproduct

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A B : PresentedAffinoidAlgebra K)

/-- The finite presentation maps into the genuine projective completion
by the two actual original tensor legs. -/
def toCompletedTensor :
    BoundedAlgHom K (algebra K A B) (CompletedTensorAlgebra.Algebra K A B) :=
  lift K (CompletedTensorAlgebra.Algebra K A B) A B
    (CompletedTensorAlgebra.leftMap K A B) (CompletedTensorAlgebra.rightMap K A B)

/-- The genuine completion maps into the finite presentation by the
constructed bounded universal extension of its two presentation legs. -/
def fromCompletedTensor :
    BoundedAlgHom K (CompletedTensorAlgebra.Algebra K A B) (algebra K A B) :=
  CompletedTensorAlgebra.lift (leftMap K A B) (rightMap K A B)

@[simp]
theorem toCompletedTensor_comp_leftMap :
    (toCompletedTensor K A B).comp (leftMap K A B) =
      CompletedTensorAlgebra.leftMap K A B :=
  lift_comp_leftMap K (CompletedTensorAlgebra.Algebra K A B) A B _ _

@[simp]
theorem toCompletedTensor_comp_rightMap :
    (toCompletedTensor K A B).comp (rightMap K A B) =
      CompletedTensorAlgebra.rightMap K A B :=
  lift_comp_rightMap K (CompletedTensorAlgebra.Algebra K A B) A B _ _

@[simp]
theorem fromCompletedTensor_comp_leftMap :
    (fromCompletedTensor K A B).comp (CompletedTensorAlgebra.leftMap K A B) =
      leftMap K A B :=
  CompletedTensorAlgebra.lift_comp_leftMap _ _

@[simp]
theorem fromCompletedTensor_comp_rightMap :
    (fromCompletedTensor K A B).comp (CompletedTensorAlgebra.rightMap K A B) =
      rightMap K A B :=
  CompletedTensorAlgebra.lift_comp_rightMap _ _

/-- The finite-presentation inverse law is equality of full bounded maps,
detected by its two entire original legs. -/
theorem fromCompletedTensor_comp_toCompletedTensor :
    (fromCompletedTensor K A B).comp (toCompletedTensor K A B) =
      BoundedAlgHom.id K (algebra K A B) := by
  apply hom_ext K (algebra K A B) A B
  · exact (congrArg
      (fun f : BoundedAlgHom K A (CompletedTensorAlgebra.Algebra K A B) =>
        (fromCompletedTensor K A B).comp f)
      (toCompletedTensor_comp_leftMap K A B)).trans
        ((fromCompletedTensor_comp_leftMap K A B).trans (BoundedAlgHom.id_comp _).symm)
  · exact (congrArg
      (fun f : BoundedAlgHom K B (CompletedTensorAlgebra.Algebra K A B) =>
        (fromCompletedTensor K A B).comp f)
      (toCompletedTensor_comp_rightMap K A B)).trans
        ((fromCompletedTensor_comp_rightMap K A B).trans (BoundedAlgHom.id_comp _).symm)

/-- The completed-tensor inverse law uses algebraic tensor generation and
density through the proved full completed-map extensionality theorem. -/
theorem toCompletedTensor_comp_fromCompletedTensor :
    (toCompletedTensor K A B).comp (fromCompletedTensor K A B) =
      BoundedAlgHom.id K (CompletedTensorAlgebra.Algebra K A B) := by
  apply CompletedTensorAlgebra.hom_ext
  · exact (congrArg
      (fun f : BoundedAlgHom K A (algebra K A B) =>
        (toCompletedTensor K A B).comp f)
      (fromCompletedTensor_comp_leftMap K A B)).trans
        ((toCompletedTensor_comp_leftMap K A B).trans (BoundedAlgHom.id_comp _).symm)
  · exact (congrArg
      (fun f : BoundedAlgHom K B (algebra K A B) =>
        (toCompletedTensor K A B).comp f)
      (fromCompletedTensor_comp_rightMap K A B)).trans
        ((toCompletedTensor_comp_rightMap K A B).trans (BoundedAlgHom.id_comp _).symm)

/-- The actual finite closed weighted Tate quotient is bounded equivalent
to the actual projective completed tensor, with both maps constructed. -/
def completedTensorEquiv :
    BoundedAlgEquiv K (algebra K A B) (CompletedTensorAlgebra.Algebra K A B) :=
  BoundedAlgEquiv.ofHomInv (toCompletedTensor K A B) (fromCompletedTensor K A B)
    (fun x => congrArg (fun f : BoundedAlgHom K (algebra K A B) (algebra K A B) => f x)
      (fromCompletedTensor_comp_toCompletedTensor K A B))
    (fun x => congrArg
      (fun f : BoundedAlgHom K (CompletedTensorAlgebra.Algebra K A B)
        (CompletedTensorAlgebra.Algebra K A B) => f x)
      (toCompletedTensor_comp_fromCompletedTensor K A B))

@[simp]
theorem completedTensorEquiv_toBoundedAlgHom :
    (completedTensorEquiv K A B).toBoundedAlgHom = toCompletedTensor K A B := rfl

@[simp]
theorem completedTensorEquiv_symm_toBoundedAlgHom :
    (completedTensorEquiv K A B).symm.toBoundedAlgHom = fromCompletedTensor K A B := rfl

/-- The genuine completed tensor spectrum is homeomorphic to the spectrum
of its actual finite affinoid presentation. -/
def completedTensorSpectrumHomeomorph :
    BanachSpectrum (CompletedTensorAlgebra.Algebra K A B) ≃ₜ
      BanachSpectrum (algebra K A B) :=
  (completedTensorEquiv K A B).spectrumHomeomorph

variable {E : Type v} [NormedCommRing E] [NormedAlgebra K E]
  [IsUltrametricDist E] [CompleteSpace E]
  (α : BoundedAlgHom K A E) (β : BoundedAlgHom K B E)

/-- Under the actual comparison, every presentation lift is precisely the
genuine completed-tensor lift with the same original bounded maps. -/
theorem lift_comp_fromCompletedTensor :
    (lift K E A B α β).comp (fromCompletedTensor K A B) =
      CompletedTensorAlgebra.lift α β := by
  apply CompletedTensorAlgebra.hom_ext
  · exact (congrArg (fun f : BoundedAlgHom K A (algebra K A B) =>
      (lift K E A B α β).comp f) (fromCompletedTensor_comp_leftMap K A B)).trans
        ((lift_comp_leftMap K E A B α β).trans
          (CompletedTensorAlgebra.lift_comp_leftMap α β).symm)
  · exact (congrArg (fun f : BoundedAlgHom K B (algebra K A B) =>
      (lift K E A B α β).comp f) (fromCompletedTensor_comp_rightMap K A B)).trans
        ((lift_comp_rightMap K E A B α β).trans
          (CompletedTensorAlgebra.lift_comp_rightMap α β).symm)

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidCoproduct
