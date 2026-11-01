import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-! # Multiplicative domination of normalized ultrametric ring seminorms -/

universe u

namespace Langlands.Analytic.BanachSpectrum

/-- Every normalized nonarchimedean ring seminorm on a commutative ring
dominates a normalized nonarchimedean multiplicative ring seminorm. -/
def NonarchimedeanDominationStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (p : RingSeminorm A),
    p 1 = 1 → IsNonarchimedean p →
    ∃ q : MulRingSeminorm A, IsNonarchimedean q ∧ ∀ a, q a ≤ p a

end Langlands.Analytic.BanachSpectrum
