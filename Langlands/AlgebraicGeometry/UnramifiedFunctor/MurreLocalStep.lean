import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepReduction
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreArtinianBase
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteLocalStepProof
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompletionDescentProof

/-! # The local step of Murre's induction

Bourbaki exp. 294 (Murre), Section 2, Case I, Steps 1, 2a and 2b: given Murre's criterion over
every locally noetherian base all of whose local rings have dimension `< n`, the criterion holds
over the spectrum of a local noetherian ring of dimension `n`. The theorem combines the proofs
of the three steps through the reduction `murreLocalStep_of_parts`. -/

universe u v

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- The local step of Murre's induction (Bourbaki exp. 294, Steps 1, 2a and 2b of Case I). -/
theorem murreLocalStep : MurreLocalStepStatement.{u, v} :=
  murreLocalStep_of_parts ⟨murreArtinianBase, murreCompleteLocalStep, murreCompletionDescent⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor
