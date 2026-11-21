import Langlands.Global.RankinSelberg.EqualFactorizationAtStatement
import Langlands.Global.RankinSelberg.EqualInfinitePlaceTests
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceModelTCStatement

/-! # Equal-rank pointwise factorization from complex place tests and the TC slice comparison -/

universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The equal-rank pointwise factorization over totally complex fields follows from the
actual Whittaker slice comparison over those fields and the tests at complex places. -/
def EqualPointwiseFactorizationTCReductionStatement : Prop :=
  InfiniteWhittakerSliceModelTCStatement.{u, uQ} →
    ComplexEqualPlaceTestsStatement.{u} →
      EqualPointwiseFactorizationTCStatement.{u, uQ}

end Langlands.Global.RankinSelbergGlobal
