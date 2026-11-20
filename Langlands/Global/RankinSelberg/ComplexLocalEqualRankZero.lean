import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZeroReduction
import Langlands.LocalFactor.Archimedean.ComplexTateProof

/-! # The complex equal-rank local equation for `GL₁ × GL₁` -/

namespace Langlands.Global.RankinSelbergGlobal

/-- All clauses of the complex equal-rank local functional equation at rank index zero. -/
def ComplexLocalEqualRankZeroStatement : Prop :=
  ComplexLocalEqualAtRankStatement 0

theorem complexLocalEqualRankZero : ComplexLocalEqualRankZeroStatement :=
  complexLocalEqualAtRankStatement_zero
    Langlands.LocalFactor.ComplexTate.complexArchimedeanTateStatement

end Langlands.Global.RankinSelbergGlobal
