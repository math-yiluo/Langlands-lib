import Langlands.Global.RankinSelberg.RealWhittakerModelUniformityStatement
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth

/-!
# One growth exponent for every real Whittaker coefficient map: proof

A proof of `Langlands.Global.RankinSelbergGlobal.RealWhittakerModelUniformityStatement`. It is
the inequality half of the Library's equality `realWhittakerModels_eq` (module
`RealWhittakerUniformGrowth`), which identifies `realWhittakerModel r ds a` with
`realUniformWhittakerModel r ds a` for every real block list `ds` of total rank `r + 1`. See the
paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- **One growth exponent for real Whittaker coefficients.** For every real block list `ds` of
total rank `r + 1` and every nonzero real `a`, the real Whittaker coefficient space
`realWhittakerModel r ds a` lies in the uniform coefficient space
`realUniformWhittakerModel r ds a`. -/
theorem realWhittakerModelUniformity : RealWhittakerModelUniformityStatement :=
  fun r ds hRank a => (realWhittakerModels_eq r ds hRank a).le

end Langlands.Global.RankinSelbergGlobal
