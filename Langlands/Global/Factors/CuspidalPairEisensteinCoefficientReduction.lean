import Langlands.Global.Factors.CuspidalPairEisensteinCoefficientStatement
import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingStatement
import Langlands.Global.Factors.CuspidalPairEisensteinLocalNumeratorStatement

/-! # Shahidi's generic coefficient identity from unfolding and the local numerator

The unfolding of the generic coefficient to the open-cell integral
(`CuspidalPairEisensteinUnfoldingStatement`) and the local numerator of that integral
(`CuspidalPairEisensteinLocalNumeratorStatement`), together with the absolute convergence of
the partial Euler product (`RankinSelbergGlobal.exists_partialEulerFactor_convergence`), give
`CuspidalPairEisensteinCoefficientStatement`. See the paired Markdown. -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

/-- The unfolding statement and the local numerator statement imply Shahidi's generic
coefficient identity. -/
def CuspidalPairEisensteinCoefficientReductionStatement : Prop :=
  CuspidalPairEisensteinUnfoldingStatement.{u} →
    CuspidalPairEisensteinLocalNumeratorStatement.{u, uQ} →
      CuspidalPairEisensteinCoefficientStatement.{u, uQ}

theorem cuspidalPairEisensteinCoefficientReduction :
    CuspidalPairEisensteinCoefficientReductionStatement.{u, uQ} := by
  intro hUnfold hLocal F _ _ _ r t T T' hT hT' P P' S hP hP' ψ hψ
  obtain ⟨S₀, hS, hnum⟩ := hLocal F r t T T' hT hT' P P' S hP hP' ψ hψ
  obtain ⟨κ, hκ, hunf⟩ := hUnfold F r t T T' hT hT' ψ hψ
  obtain ⟨σL, hL⟩ := RankinSelbergGlobal.exists_partialEulerFactor_convergence P P'
    (hP.trans hS) (hP'.trans hS)
  refine ⟨S₀, hS, fun s₀ hs₀ => ?_⟩
  obtain ⟨φ, hφ, c, hc, hcs₀, hc₀, σN, hcN⟩ := hnum s₀ hs₀
  obtain ⟨σU, hcU⟩ := hunf φ hφ
  have hκ' : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
  refine ⟨φ, hφ, fun s => (κ : ℂ) * c s, ?_, analyticAt_const.mul hcs₀,
    mul_ne_zero hκ' hc₀, max σL (max σU σN), fun s hs => ?_⟩
  · intro x hx
    exact (MeromorphicAt.const (κ : ℂ) x).mul (hc x hx)
  · have hσL : σL < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hσU : σU < s.re :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
    have hσN : σN < s.re :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
    have h1 : σL < (1 + s).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    obtain ⟨hsum, hprod⟩ := hL (1 + s) h1
    refine ⟨hsum, _, hprod, ?_⟩
    show (κ : ℂ) * c s = _
    rw [hcN s hσN, hcU s hσU]
    ring

end Langlands.Global
