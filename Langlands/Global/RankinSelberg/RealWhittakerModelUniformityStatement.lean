import Langlands.Global.RankinSelberg.RealUniformWhittakerModel

/-! # One growth exponent for every real Whittaker coefficient map -/

noncomputable section

set_option autoImplicit false

open Langlands.LocalFactor.Archimedean

namespace Langlands.Global.RankinSelbergGlobal

/-- Every function in the real Whittaker coefficient space of a real block list of total rank
`r + 1` lies in the uniform coefficient space of the same list and character, whose generating
coefficient maps have one polynomial growth exponent for all source vectors. -/
def RealWhittakerModelUniformityStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ a : ℝˣ,
    realWhittakerModel r ds a ≤ realUniformWhittakerModel r ds a

end Langlands.Global.RankinSelbergGlobal
