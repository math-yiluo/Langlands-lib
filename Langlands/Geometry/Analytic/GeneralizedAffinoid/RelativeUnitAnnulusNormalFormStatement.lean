import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulus
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.Int

/-! # A Laurent coefficient normal form for the actual relative unit annulus -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus

open scoped ZeroAtInfty

/-- A coefficient normal form, with the original annulus quotient norm and canonical maps. -/
def NormalFormStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K),
    ∃ e : Algebra K A ≃ₗᵢ[K] C₀(ℤ, A),
      (∀ (a : A) (i j : ℕ) (n : ℤ),
        e (baseMap K A a * annulusX K A ^ i * annulusY K A ^ j) n =
          if n = (i : ℤ) - (j : ℤ) then a else 0) ∧
      (∀ (z : Algebra K A) (n : ℤ),
        e (annulusX K A * z) n = e z (n - 1)) ∧
      (∀ (z : Algebra K A) (n : ℤ),
        e (annulusY K A * z) n = e z (n + 1)) ∧
      (∀ (a : A) (z : Algebra K A) (n : ℤ),
        e (baseMap K A a * z) n = a * e z n) ∧
      (∀ (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) (n : ℤ),
        e (positive K A h) n =
          if 0 ≤ n then
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n.toNat)
              (GeneralizedTateAlgebra.series (PositivePolyradius.unit (Fin 1)) A h)
          else 0) ∧
      (∀ (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 1)) A) (n : ℤ),
        e (negative K A h) n =
          if n ≤ 0 then
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) (-n).toNat)
              (GeneralizedTateAlgebra.series (PositivePolyradius.unit (Fin 1)) A h)
          else 0)

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus
