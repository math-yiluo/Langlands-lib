import Langlands.Global.ArthurTruncationIdempotence
import Langlands.Global.ArthurTruncationUniformWeylHeight
import Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingProof

/-! # Arthur's pointwise truncation theorem for every compact Iwasawa subgroup -/

universe u

namespace Langlands.Global.ArthurTruncation

open Idempotence

/-- **Arthur 2005, Proposition 13.1(a),(b)** for every compact Iwasawa subgroup. -/
theorem iwasawaTruncationIdempotent : IwasawaTruncationIdempotentStatement.{u} := by
  intro F _ _ G _ _ T i _ ν hG hi hν D K hK hρ
  exact isTruncationIdempotent_of_unfolding_of_weylHeight hG hi hν D hK hρ geometricLemmaUnfolding
    (fun β n => exists_weylHeight_lowerBound hG hi hν D hK hρ β _
      (isRealFundamentalWeight hG hi hν D β) n)

end Langlands.Global.ArthurTruncation
