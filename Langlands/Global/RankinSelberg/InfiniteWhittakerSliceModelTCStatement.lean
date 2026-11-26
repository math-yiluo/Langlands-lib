import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerSliceReduction

/-! # The actual archimedean Whittaker slice comparison over totally complex fields

The Whittaker slice comparison `InfiniteWhittakerSliceModelAt` over all totally complex fields.
-/

open NumberField
set_option autoImplicit false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

/-- The actual archimedean Whittaker slice comparison for each totally complex field.
There are no real places, but the same `ModelData` is used. -/
def InfiniteWhittakerSliceModelTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    InfiniteWhittakerSliceModelAt.{u, uQ} F

end Langlands.Global.RankinSelbergGlobal
