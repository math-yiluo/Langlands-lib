import Langlands.Global.RankinSelberg.UnequalFactorizationAtStatement
import Langlands.Global.RankinSelberg.UnequalInfinitePlaceTests
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceModelTCStatement

/-! # Unequal-rank pointwise factorization from complex place tests and the TC slice comparison -/

universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The unequal-rank pointwise factorization over totally complex fields follows from the
actual Whittaker slice comparison over those fields and the unequal-rank tests at complex
places. -/
def UnequalPointwiseFactorizationTCReductionStatement : Prop :=
  InfiniteWhittakerSliceModelTCStatement.{u, uQ} →
    ComplexUnequalPlaceTestsStatement.{u} →
      UnequalPointwiseFactorizationTCStatement.{u, uQ}

end Langlands.Global.RankinSelbergGlobal
