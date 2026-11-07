import Langlands.GroupScheme.Absolute.BruhatCoveringReduction
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.ParabolicQuotientProperProof
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof

/-! # Absolute Bruhat covering for an actual Borel pair

The proof of `AbsoluteBruhatCoveringStatement`: the dynamic-limit reduction
`absoluteBruhatCovering_of_prerequisites` applied to the Library proofs of its seven
structure-theory prerequisites. -/

universe u

namespace Langlands.GroupScheme

/-- **Absolute Bruhat covering** (Borel–Tits 1965, §2.4). For a Borel pair `(B, T)` of a
connected reductive group `G` over an algebraically closed field, every rational point of `G`
lies in `B(k) n B(k)` for a rational point `n` normalizing `T`. -/
theorem absoluteBruhatCovering : AbsoluteBruhatCoveringStatement.{u} :=
  absoluteBruhatCovering_of_prerequisites
    ⟨torusFiniteGaloisSplitting, regularCocharacterBorel, genericCentralizer,
      maximalTorusCentralizer, parabolicSubgroupQuotientProper, centralizerBorelIntersection,
      solvableMaximalTorusConjugacy⟩

end Langlands.GroupScheme
