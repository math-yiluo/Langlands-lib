import Langlands.Representation.Character.ExactAdditivityProof

/-! # The actual character map on the exact finite-length Grothendieck group -/

noncomputable section

universe uG uV

namespace Langlands.Character

/-- Under actual finite-length admissibility, the actual character extends
uniquely over every relation of the exact Grothendieck group. -/
theorem exactK0CharacterRealization :
    ExactK0CharacterRealizationStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ hAdm
  let a : SmoothRep.FiniteLengthIsoClass.{0, uG, uV} ℂ G →
      HarmonicAnalysis.Distribution G :=
    Quotient.lift
      (fun A : SmoothRep.FiniteLengthObject.{0, uG, uV} ℂ G =>
        distribution μ A.val.representation (hAdm A.val A.property))
      (by
        intro A B h
        obtain ⟨e⟩ := h
        let E := SmoothRep.equivOfIso e
        exact distribution_eq_of_equivariant μ A.val.representation
          (hAdm A.val A.property) B.val.representation (hAdm B.val B.property)
          E.toLinearEquiv E.toIntertwiningMap.isIntertwining)
  have ha : SmoothRep.FiniteLengthGrothendieckGroup.IsExactAdditive ℂ G a := by
    intro A B C f g h
    exact distributionShortExactAdditivity G μ A.val B.val C.val
      (hAdm A.val A.property) (hAdm B.val B.property) (hAdm C.val C.property) f g h
  refine ⟨SmoothRep.FiniteLengthGrothendieckGroup.lift ℂ G a ha, ?_, ?_⟩
  · intro A hA
    exact SmoothRep.FiniteLengthGrothendieckGroup.lift_ofRepresentation ℂ G a ha A hA
  · intro χ hχ
    apply SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object ℂ G
    intro A
    exact (hχ A.val A.property).trans
      (SmoothRep.FiniteLengthGrothendieckGroup.lift_ofObject ℂ G a ha A).symm

end Langlands.Character
