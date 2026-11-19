import Langlands.AlgebraicGeometry.Picard.RosatiPositivityStatement
import Langlands.AlgebraicGeometry.Picard.RosatiPositivityReduction
import Langlands.AlgebraicGeometry.Picard.RosatiTraceSymmetry
import Langlands.AlgebraicGeometry.Picard.RosatiMumfordIntegralPositivity
import Langlands.AlgebraicGeometry.Picard.RosatiGeometricDescent
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceProof
import Langlands.AlgebraicGeometry.Picard.NonzeroEndomorphismMixedEulerPositiveProof

/-! # Positivity of the actual geometric Rosati trace form -/

universe u

namespace Langlands.AbelianScheme.Rosati

/-- The fixed trace form of every actual geometric polarization is symmetric
and positive definite, in the full universe of `PositivityStatement`. -/
theorem positivity : PositivityStatement.{u} := by
  have hample : AmplePresentationIntegralPositiveStatement.{u} :=
    integralDiagonalPositive_of_ampleMumfordPresentation
      mumfordMixedEulerTrace nonzeroEndomorphismMixedEulerPositive
  have hgeom : GeometricPolarizationIntegralPositiveStatement.{u} :=
    geometricPolarizationIntegralPositive_of_amplePresentation hample
  intro P k instField instClosed instChar A W hadd lam hpol hinv
  have hstrict := traceForm_pos_of_integral A P W hadd lam
    (@hgeom P k instField instClosed instChar A W hadd lam hinv hpol)
  refine ⟨traceForm_symm P W hadd lam hpol, ?_, ?_⟩
  · intro a
    by_cases ha : a = 0
    · simp [ha]
    · exact (hstrict a ha).le
  · intro a ha
    simpa only [traceForm_apply] using hstrict a ha

end Langlands.AbelianScheme.Rosati
