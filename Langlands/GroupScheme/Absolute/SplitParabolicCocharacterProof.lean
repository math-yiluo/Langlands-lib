import Langlands.GroupScheme.Absolute.SplitParabolicCocharacterAbsoluteReduction
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelOvergroupCocharacterProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Proof: split parabolics containing a fixed maximal torus are dynamic -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- **Split parabolic classification with a fixed torus.** Every geometric parabolic
containing a split maximal torus of a connected reductive group over a field is the
dynamic subgroup of an actual integral cocharacter of that same torus, as an equality
of subgroup functors on every test scheme. -/
theorem splitParabolicCocharacterStatement : SplitParabolicCocharacterStatement.{u} :=
  splitParabolicCocharacterStatement_of_absoluteBorelOvergroup
    borelConjugacy absoluteBorelOvergroupCocharacter maximalTorusBaseChange

end Langlands.GroupScheme
