import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingReduction
import Langlands.Global.Factors.CuspidalPairEisensteinCoefficientStatement
import Langlands.Global.Factors.CuspidalPairEisensteinHolomorphyStatement
import Langlands.Global.Factors.EulerProductCoefficientDataReduction
import Langlands.Global.RankinSelberg.EqualAnalyticCharacter

/-! # Shahidi's boundary nonvanishing from the generic coefficient

The coefficient identity and its imaginary-axis holomorphy give both existence of the
partial pair L-function and nonpositive order on `Re s = 1`, by the Euler-product
coefficient-data and finite-factor reductions. See the paired Markdown for the two
retained automorphic inputs and the source comparison. -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open RankinSelbergGlobal.EqualAnalytic

/-- The two Eisenstein coefficient inputs give a partial pair L-function with
nonpositive order on the boundary line for one enlarged omitted set. -/
theorem cuspidalPairBoundaryNonvanishingEnlarged_of_eisenstein
    (hCoefficient : CuspidalPairEisensteinCoefficientStatement.{u, uQ})
    (hHolomorphy : CuspidalPairEisensteinHolomorphyStatement.{u}) :
    CuspidalPairBoundaryNonvanishingEnlargedStatement.{u, uQ} := by
  intro F _ _ _ r t T T' hT hT' P P' S hP hP'
  let ψ := standardCharacter F
  have hψ : IsStandardAdditiveCharacter F ψ := by
    refine ⟨continuous_standardCharacter F, ?_, standardCharacter_algebraMap F, ?_⟩
    · intro he
      obtain ⟨x, hx⟩ := Automorphic.CuspidalWhittaker.exists_adelicCharacter_ne_one F
      apply hx
      apply (standardCharacter_eq_one_iff F x).mp
      change ψ x = 1
      rw [he, AddChar.one_apply]
    · intro x
      change ‖standardCharacter F x‖ = 1
      rw [standardCharacter_apply, Circle.norm_coe]
  obtain ⟨S₀, hS, hdata⟩ := hCoefficient F r t T T' hT hT' P P' S hP hP' ψ hψ
  apply EulerProductCoefficientData.enlarged_of_coefficientData (P := P) (P' := P') hP hP' hS
  intro s₀ hs₀
  obtain ⟨φ, hφ, c, hc, hcs₀, hc₀, hfactor⟩ := hdata s₀ hs₀
  obtain ⟨Ec, hEc, haxis, hagree⟩ := hHolomorphy F r t T T' hT hT' ψ hψ φ hφ
  have heq : s₀ = (s₀.im : ℂ) * Complex.I := by
    simpa [hs₀] using (Complex.re_add_im s₀).symm
  exact ⟨CuspidalPairEisenstein.coeff (r := r) (t := t) ψ φ, c, Ec,
    meromorphicOn_univ.mp hc, hcs₀, hc₀, meromorphicOn_univ.mp hEc,
    heq ▸ haxis s₀.im, hfactor, hagree⟩

/-- Shahidi's boundary nonvanishing for every admissible omitted set, conditional on
the generic coefficient identity and the continuation and axis holomorphy of that coefficient. -/
def CuspidalPairEisensteinDerivationStatement : Prop :=
  CuspidalPairEisensteinCoefficientStatement.{u, uQ} →
    CuspidalPairEisensteinHolomorphyStatement.{u} →
    CuspidalPairBoundaryNonvanishingStatement.{u, uQ}

/-- **`CuspidalPairEisensteinDerivationStatement`.** -/
theorem cuspidalPairEisensteinDerivation : CuspidalPairEisensteinDerivationStatement.{u, uQ} :=
  fun hCoefficient hHolomorphy => cuspidalPairBoundaryNonvanishingReduction
    (cuspidalPairBoundaryNonvanishingEnlarged_of_eisenstein hCoefficient hHolomorphy)

end Langlands.Global
