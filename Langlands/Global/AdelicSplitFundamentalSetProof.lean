import Langlands.Global.AdelicSplitFundamentalSetFromCover

/-! # Exact proof of Springer's split adelic fundamental-set statement -/

universe u

namespace Langlands.Global.AdelicSiegelFactors

/-- Springer's split adelic fundamental-set theorem, with the exact published
statement as its type, in arbitrary universe `u`. -/
theorem splitAdelicFundamentalSetProof : SplitAdelicFundamentalSetStatement.{u} :=
  splitAdelicFundamentalSet

end Langlands.Global.AdelicSiegelFactors
