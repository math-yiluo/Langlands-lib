import Langlands.Representation.Archimedean.RealMixedSwapIntertwiner
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages

/-!
# The unlinked induction-character swap
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- The full induction-character unlinked swap, including arbitrary surrounding blocks. -/
theorem realInducedCharacterSwap : RealInducedCharacterSwapStatement := by
  intro n pre post d b hd hrank hord hun
  have h := RealMixedSwapTwist.inducedCharacterSwap_unlinked d b hd hord hun
  simpa using h.in_stages pre post rfl rfl (by simpa using hrank)

end Langlands.Archimedean
