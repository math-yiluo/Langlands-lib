import Langlands.Automorphic.GeneralLinearSummandFormsIrreducibleProof

/-! # The summand-to-realization theorem for `GL_n` from the density input alone -/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- Density of the classes of attached stable cusp forms in every irreducible cuspidal summand
implies the summand-to-realization direction of Getz–Hahn, Theorem 9.7.3. -/
def GeneralLinearCuspidalSummandRealizationFromDensityStatement : Prop :=
  GeneralLinearSummandFormsDenseStatement.{u} →
    GeneralLinearCuspidalSummandRealizationStatement.{u}

/-- The published reduction applied to the proved differential stability and algebraic
irreducibility inputs. -/
theorem generalLinearCuspidalSummandRealizationFromDensity :
    GeneralLinearCuspidalSummandRealizationFromDensityStatement.{u} := fun hDense =>
  generalLinearCuspidalSummandRealizationReduction generalLinearSummandFormsEnveloping hDense
    generalLinearSummandFormsIrreducible

end Langlands.Automorphic.GroupSchemeFunctions
