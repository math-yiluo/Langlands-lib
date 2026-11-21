import Langlands.GroupScheme.SimplyConnected.SplitPicardTrivialCoverReduction
import Langlands.GroupScheme.SimplyConnected.SplitFactorialProof

/-! # A Picard-trivial central cover of a split semisimple group -/

universe u

namespace Langlands.GroupScheme

/-- **A Picard-trivial central cover** (Iversen's theorem, split semisimple case;
Milne, *Algebraic Groups* (2017), Proposition 18.22). -/
theorem splitSemisimplePicardTrivialCover : SplitSemisimplePicardTrivialCoverStatement.{u} :=
  splitSemisimplePicardTrivialCover_of_factorial splitSimplyConnectedFactorial

end Langlands.GroupScheme
