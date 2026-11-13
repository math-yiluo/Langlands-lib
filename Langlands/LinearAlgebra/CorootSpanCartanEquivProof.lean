import Langlands.LinearAlgebra.CorootSpanCartanEquivStatement
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv

/-! # Based root data with spanning coroots are determined by their Cartan matrix: proof -/

universe u

namespace Langlands.LinearAlgebra

/-- Two finite reduced root data with spanning coroots whose bases are related by a
bijection preserving the simple pairings are isomorphic by an equivalence extending it. -/
theorem corootSpanCartanEquiv : CorootSpanCartanEquivStatement.{u} := by
  intro ι M N ι' M' N' _ _ _ _ _ _ P Q _ _ b c hP hQ e he
  exact Langlands.RootDatumSimpleCorootEquiv.exists_equiv_indexEquiv b c hP hQ e he

end Langlands.LinearAlgebra
