import Langlands.CommutativeAlgebra.MvPowerSeriesFieldFactorialStatement
import Langlands.CommutativeAlgebra.MvPowerSeriesFactorial
import Langlands.CommutativeAlgebra.MvPowerSeriesCoordinateChange
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! # Proof: formal power series in finitely many variables over a field are factorial -/

universe u v

namespace Langlands.CommutativeAlgebra

/-- For every field `K` and every finite type `σ`, `MvPowerSeries σ K` is a unique factorization
monoid. The case `σ = Fin n` is
`MvPowerSeriesFactorial.uniqueFactorizationMonoid_of_coord` with the coordinate change
`MvPowerSeriesFactorial.exists_algEquiv_coeff_single_zero_ne_zero`; a general finite `σ` is
reduced to it by renaming the variables along `σ ≃ Fin (Fintype.card σ)`. -/
theorem mvPowerSeriesFieldFactorial : MvPowerSeriesFieldFactorial.{u, v} := by
  intro K _ σ _
  cases nonempty_fintype σ
  have hfin : UniqueFactorizationMonoid (MvPowerSeries (Fin (Fintype.card σ)) K) :=
    MvPowerSeriesFactorial.uniqueFactorizationMonoid_of_coord K
      (fun _ _ hf => MvPowerSeriesFactorial.exists_algEquiv_coeff_single_zero_ne_zero hf)
      (Fintype.card σ)
  exact (MvPowerSeries.renameEquiv K (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid
    hfin

end Langlands.CommutativeAlgebra
