import Langlands.Representation.RankinSelberg.HighlyRamified.Duality
import Langlands.Representation.RankinSelberg.HighlyRamified.RankOne
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof

/-!
# Gamma factors against the trivial character after a highly ramified twist

`UniformRankOneTwistStatement` gives `L(s, (τ ⊗ η ∘ det) × 1) = 1` and
`ε(s, (τ ⊗ η ∘ det) × 1, ψ) = c q^(-(n+1) a(η) s)` once `a(η)` is large, uniformly
for generic `τ` of rank `n + 1` with a given principal level. Applied to the inverse
transpose of `τ` and to `ψ⁻¹`, it also gives `L = 1` on the dual side. So the gamma
factor is the monomial `c X^((n+1) a(η))` (`symmetricGammaExpression`).
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-- The gamma expression with trivial `L`-polynomials is the epsilon monomial. -/
theorem rationalGammaExpression_one_one (δ c : ℂˣ) (m : ℤ) :
    rationalGammaExpression δ c m 1 1 = (rationalEpsilonMonomial c m : RationalFunctions) := by
  simp [rationalGammaExpression]

/-- For each rank `n + 1` and level `f` there is `B` such that, for every generic `τ`
of rank `n + 1` with a level-`f` vector and every quasicharacter `η` with
`a(η) ≥ B`, every gamma factor of `(τ ⊗ η ∘ det, 1)` is `c X^((n+1) a(η))` for some
`c : ℂˣ`. -/
theorem exists_bound_rankOne_gammaMonomial (h : UniformRankOneTwistStatement.{uF, uV})
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0) (n f : ℕ) :
    ∃ B : ℕ, ∀ {X : Type uV} [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) X),
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ n τ) →
      HasPrincipalLevelVector F τ f →
      ∀ η : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
        B ≤ F.canonicalTopologicalData.multiplicativeConductor η →
        ∀ G : RationalFunctions,
          IsPadicSymmetricGammaFactor F ψ ν.val
            (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
            (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G →
          ∃ c : ℂˣ, G = rationalEpsilonMonomial c
            (((n + 1) * F.canonicalTopologicalData.multiplicativeConductor η : ℕ) : ℤ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨B₁, h₁, -⟩ := h p F ψ ν hψ n f
  obtain ⟨B₂, h₂, -⟩ := h p F (ψ.scale (-1)) (DominantRankTransport.negatedSelfDualHaar F ψ ν)
    ((additiveConductor_scale_neg_one F ψ).trans hψ) n f
  refine ⟨max B₁ B₂, ?_⟩
  intro X _ _ τ hτ hf η hη G hG
  obtain ⟨hP, c, hε⟩ := h₁ τ hτ hf η (le_of_max_le_left hη)
  obtain ⟨hPd, -⟩ := h₂ (inverseTransposePullback τ) (isGeneric_inverseTransposePullback F ψ τ hτ)
    (hasPrincipalLevelVector_inverseTransposePullback F τ hf) η⁻¹
    ((multiplicativeConductor_inv F η).symm ▸ le_of_max_le_right hη)
  have hPd' : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ))
      (inverseTransposePullback (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))) 1 :=
    (IsPadicSymmetricLPolynomial.congr_equiv
      (inverseTransposePullbackTwistEquiv F τ (η : F.Carrierˣ →* ℂˣ)).symm
      (inverseTransposePullbackTrivialEquiv F).symm).mp hPd
  have hW : IsOfWhittakerType n (standardCharacter ψ n)
      (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ) :=
    isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ η hτ)
  have hinput := whittakerTypeGammaConstructionInput p F ψ ν n 0 X ℂ
    (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hW (rankOneCharacter_isOfWhittakerType p F ψ 1)
  have hG' := (symmetricGammaExpression p F ψ ν n 0 _ _ hinput _ 1 1 hε hP hPd' G).mp hG
  exact ⟨c, hG'.trans (rationalGammaExpression_one_one _ _ _)⟩

end Langlands.RankinSelberg.HighlyRamified
