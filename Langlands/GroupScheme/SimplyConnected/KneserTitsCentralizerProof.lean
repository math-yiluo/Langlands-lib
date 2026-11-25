import Langlands.GroupScheme.SimplyConnected.KneserTitsCentralizerStatement
import Langlands.GroupScheme.SimplyConnected.KneserTitsCentralizerReduction
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationProof
import Langlands.GroupScheme.SimplyConnected.KneserTitsFactorProof
import Langlands.GroupScheme.SimplyConnected.AnisotropicFactorCentralizerProof

/-! # Kneser–Tits for split-torus centralizers in simply connected groups: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Kneser–Tits for split-torus centralizers.** Over a nonarchimedean local field, the
rational points of the centralizer `Z` of a maximal split torus of a simply connected group lie
in the product of `Z(F) ∩ G(F)^+` and the common kernel `Z(F)^1` of the absolute values of the
rational characters of `Z`. -/
theorem simplyConnectedKneserTitsCentralizer :
    SimplyConnectedKneserTitsCentralizerStatement.{u} :=
  simplyConnectedKneserTitsCentralizer_of_factors simplyConnectedAlmostSimpleRationalGeneration
    simplyConnectedKneserTitsFactor simplyConnectedAnisotropicFactorCentralizer

end Langlands.GroupScheme
