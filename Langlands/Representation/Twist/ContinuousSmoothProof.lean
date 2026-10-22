import Langlands.Representation.Twist.ContinuousSmoothStatement
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Representation.Twist.SmoothProof

namespace Langlands

universe uG uV

variable {G : Type uG} {V : Type uV}
variable [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

/-- A continuous complex twist preserves the smoothness of each vector. -/
theorem isSmoothVector_twist_iff_of_continuous [NonarchimedeanGroup G]
    (chi : G →* ℂˣ) (rho : Representation ℂ G V) (hchi : Continuous chi) (v : V) :
    IsSmoothVector (twist chi rho) v ↔ IsSmoothVector rho v :=
  isSmoothVector_twist_iff chi rho
    (isOpen_ker_of_continuous_complex_character chi hchi) v

/-- A continuous complex twist preserves smoothness of the representation. -/
theorem isSmooth_twist_iff_of_continuous [NonarchimedeanGroup G]
    (chi : G →* ℂˣ) (rho : Representation ℂ G V) (hchi : Continuous chi) :
    IsSmooth (twist chi rho) ↔ IsSmooth rho :=
  isSmooth_twist_iff chi rho
    (isOpen_ker_of_continuous_complex_character chi hchi)

/-- The full target, including its internally quantified nonarchimedean instance. -/
theorem continuousComplexTwistSmoothCompatibility :
    ContinuousComplexTwistSmoothCompatibility (G := G) (V := V) := by
  intro inst chi rho hchi
  exact ⟨isSmoothVector_twist_iff_of_continuous chi rho hchi,
    isSmooth_twist_iff_of_continuous chi rho hchi⟩

end Langlands
