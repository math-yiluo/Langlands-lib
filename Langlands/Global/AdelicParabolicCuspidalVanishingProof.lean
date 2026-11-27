import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof
import Langlands.Global.AdelicNormOneClassicalCuspidalDensity
import Langlands.Global.AdelicNormOneCuspidalSeparationReduction
import Langlands.Global.AdelicNormOneCuspidalVanishingReduction

/-! # Proof of the parabolic cuspidal vanishing criterion -/

universe u

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions

/-- The fibrewise cuspidal annihilator criterion for continuous moderate-growth
functions on the parabolic quotients of a connected reductive number-field group. -/
theorem parabolicCuspidalVanishing : ParabolicCuspidalVanishingStatement.{u} :=
  normOneCuspidalVanishingReduction
    (normOneCuspidalSeparation_of_classicalDensity
      (adelicNormOneClassicalCuspidalDensity_of_centerConjugation adelicEnvelopingCenterConjugation))

end Langlands.Global
