import Langlands.GroupScheme.Absolute.BorelMaximalTorusReduction
import Langlands.GroupScheme.Absolute.BorelConjugacyProof

/-! # Every Borel subgroup contains a maximal torus of the ambient group -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Every Borel subgroup of a smooth connected affine group over an algebraically closed
field belongs to a Borel pair (Milne, the paragraph after Definition 17.12). -/
theorem borelMaximalTorus : BorelMaximalTorusStatement.{u} :=
  borelMaximalTorusStatement_of_borelConjugacy borelConjugacy

end Langlands.GroupScheme
