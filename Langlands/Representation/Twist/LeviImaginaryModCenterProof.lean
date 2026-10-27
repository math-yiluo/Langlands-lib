import Langlands.Representation.Twist.LeviImaginaryModCenterStatement
import Langlands.Representation.Twist.UnitaryModCenterProof

/-! # Imaginary determinant twists preserve whole-Levi analytic predicates -/

noncomputable section

namespace Langlands

universe uF uV

/-- The complete whole-Levi imaginary-twist statement, with independent
field and representation-carrier universes. -/
theorem leviImaginaryTwistModCenter :
    LeviImaginaryTwistModCenterStatement.{uF,uV} := by
  intro p _ F T n B σ u
  let := T.topology
  let := T.leviTopologicalGroup B
  have hχ := T.isOpen_ker_leviComplexPowerCharacter B
    (fun i => Complex.I * (u i : ℂ))
  have hu := T.norm_leviComplexPowerCharacter_imaginary B u
  constructor
  · constructor
    · intro h _ _ μ _
      exact (unitaryTwistModCenter (B.Levi F.Carrier) σ.V μ σ.ρ _ hχ hu).1.mp
        (h μ)
    · intro h _ _ μ _
      exact (unitaryTwistModCenter (B.Levi F.Carrier) σ.V μ σ.ρ _ hχ hu).1.mpr
        (h μ)
  · constructor
    · intro h _ _ μ _
      exact (unitaryTwistModCenter (B.Levi F.Carrier) σ.V μ σ.ρ _ hχ hu).2.mp
        (h μ)
    · intro h _ _ μ _
      exact (unitaryTwistModCenter (B.Levi F.Carrier) σ.V μ σ.ρ _ hχ hu).2.mpr
        (h μ)

end Langlands
