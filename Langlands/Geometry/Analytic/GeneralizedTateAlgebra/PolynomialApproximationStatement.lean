import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Definitions
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # Monomial expansion and polynomial density targets -/

noncomputable section

universe u v

namespace Langlands.Analytic.GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ) (K : Type v)
  [NormedCommRing K] [IsUltrametricDist K]

/-- Finite monomial truncations converge to every restricted series, and
polynomial evaluation at its coordinate monomials has dense range. -/
def PolynomialApproximationStatement : Prop :=
  (∀ f : GeneralizedTateAlgebra r K,
    HasSum (fun d : σ →₀ ℕ =>
      monomial r K d (MvPowerSeries.coeff d (series r K f))) f) ∧
  DenseRange (MvPolynomial.aeval
    (fun i : σ => monomial r K (Finsupp.single i 1) (1 : K)) :
      MvPolynomial σ K →ₐ[K] GeneralizedTateAlgebra r K)

end Langlands.Analytic.GeneralizedTateAlgebra
