import Langlands.Representation.CuspidalSupport.CuspidalityComparisonStatement
import Langlands.Representation.Classification.SupercuspidalContragredientAux

namespace Langlands.CuspidalSupport

universe uF uV

/-- Standard parabolic Jacquet vanishing is the existing all-conjugates condition. -/
theorem standardJacquetSupercuspidalityClause {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) (n : ℕ) :
    StandardJacquetSupercuspidalityClause.{uF, uV} T n := by
  letI := T.topology
  intro V _ _ ρ
  rw [GeneralLinear.isSupercuspidal_iff_standard]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro B
  apply forall_congr'
  intro _
  exact (B.jacquetModuleEquiv ρ).toEquiv.subsingleton_congr.symm

example : ∀ {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) (n : ℕ),
    StandardJacquetSupercuspidalityClause.{uF, uV} T n :=
  @standardJacquetSupercuspidalityClause

end Langlands.CuspidalSupport
