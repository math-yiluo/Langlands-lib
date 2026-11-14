import Langlands.Representation.RankinSelberg.GammaNormalizationAlgebra

noncomputable section

namespace Langlands.RankinSelberg.TemperedLFactorGamma

open Polynomial Langlands.LocalFactor

/-- The explicit gamma expression multiplies over any finite index type. -/
theorem rationalGammaExpression_prod {ι : Type*} [Fintype ι]
    (δ : ℂˣ) (P PD : ι → ℂ[X]) (c : ι → ℂˣ) (a : ι → ℤ) :
    rationalGammaExpression δ (∏ i, c i) (∑ i, a i) (∏ i, P i) (∏ i, PD i) =
      ∏ i, rationalGammaExpression δ (c i) (a i) (P i) (PD i) := by
  classical
  have hz (s : Finset ι) :
      (RatFunc.X : RationalFunctions) ^ (∑ i ∈ s, a i) =
        ∏ i ∈ s, (RatFunc.X : RationalFunctions) ^ a i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi,
        zpow_add₀ (show (RatFunc.X : RationalFunctions) ≠ 0 from RatFunc.X_ne_zero), ih]
  simp only [rationalGammaExpression, coe_rationalEpsilonMonomial,
    map_prod, Units.coe_prod, Finset.prod_div_distrib, Finset.prod_mul_distrib, hz]

end Langlands.RankinSelberg.TemperedLFactorGamma
