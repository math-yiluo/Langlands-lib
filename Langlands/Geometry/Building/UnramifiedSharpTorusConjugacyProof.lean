import Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyReduction
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof

/-! # Sharp conjugacy of maximally split maximal tori over the unramified closure: the proof -/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Over `UnramifiedClosure F` of a nonarchimedean local field `F`, any two maximally split
maximal tori of a connected reductive group are conjugate by the image of the supplied
simply connected cover of the derived subgroup (the structural input to Kaletha–Prasad,
Lemma 2.6.24). -/
theorem unramifiedSharpTorusConjugacy : UnramifiedSharpTorusConjugacyStatement.{u} :=
  unramifiedSharpTorusConjugacy_of_structure maximalSplitTorusConjugacy
    simplyConnectedCentralizerProduct quasiSplitMaximalTorusCentralizer
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)

end Langlands.Geometry.Building
