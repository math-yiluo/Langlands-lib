import Langlands.Automorphic.GeneralLinearCuspidalMultiplicityOneReduction
import Langlands.Automorphic.CuspidalOperatorMultiplicityOneProof
import Langlands.Automorphic.GeneralLinearCuspidalSummandEquivalenceProof
import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationFromDensity
import Langlands.Automorphic.GeneralLinearSummandFormsDenseProof

/-! # Multiplicity one for the cuspidal spectrum of `GL_n` -/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- Isometrically equivalent irreducible closed invariant subspaces of the full cuspidal
`L²` space of the positive-central rational quotient of `GL_n` coincide. -/
theorem generalLinearCuspidalMultiplicityOne :
    GeneralLinearCuspidalMultiplicityOneStatement.{u} :=
  generalLinearCuspidalMultiplicityOne_of_summandEquivalence
    Langlands.Automorphic.cuspidalOperatorMultiplicityOne
    (generalLinearCuspidalSummandRealizationFromDensity generalLinearSummandFormsDense)
    generalLinearCuspidalSummandEquivalence

end Langlands.Automorphic.GroupSchemeFunctions
