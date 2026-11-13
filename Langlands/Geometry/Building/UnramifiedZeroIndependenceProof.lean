import Langlands.Geometry.Building.UnramifiedZeroIndependenceReduction
import Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyReduction
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction
import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRationalReduction
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotient

/-! # Independence of `H(K)^0` from its defining data (KP Lemma 2.6.24)

The proof composes published results. Steinberg's class quotient
(`quasiSplitSteinbergQuotient`) gives rational strongly regular classes (Borel–Springer
8.6) and then quasi-splitness over Henselian discretely valued fields with algebraically
closed residue field. Over `K = UnramifiedClosure F` this gives conjugacy of maximally
split maximal tori under `H(K)^♮`, which implies the independence statement. -/

universe u

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

/-- The target from Henselian quasi-splitness, through sharp conjugacy of maximally split
maximal tori over `UnramifiedClosure F`. -/
theorem unramifiedZeroPointsIndependence_of_henselianDiscrete
    (hhens : HenselianDiscreteQuasiSplitStatement.{u}) :
    UnramifiedZeroPointsIndependenceStatement.{u} :=
  unramifiedZeroPointsIndependence_of_sharpConjugacy
    (unramifiedSharpTorusConjugacy_of_structure maximalSplitTorusConjugacy
      simplyConnectedCentralizerProduct quasiSplitMaximalTorusCentralizer
      (unramifiedQuasiSplit_of_henselianDiscrete hhens))

/-- The target from Steinberg's class quotient for simply connected quasi-split groups. -/
theorem unramifiedZeroPointsIndependence_of_steinbergQuotient
    (h : QuasiSplitSteinbergQuotientStatement.{u}) :
    UnramifiedZeroPointsIndependenceStatement.{u} :=
  unramifiedZeroPointsIndependence_of_henselianDiscrete
    (henselianDiscreteQuasiSplitReduction (quasiSplitRegularClassRationalReduction h))

/-- **Kaletha–Prasad, Lemma 2.6.24 (independence).** The subgroup `H(K)^0` of
Definition 2.6.23(1) does not depend on the choices made to define it. -/
theorem unramifiedZeroPointsIndependence : UnramifiedZeroPointsIndependenceStatement.{u} :=
  unramifiedZeroPointsIndependence_of_steinbergQuotient quasiSplitSteinbergQuotient

end Langlands.Geometry.Building
