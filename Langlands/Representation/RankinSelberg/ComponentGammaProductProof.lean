import Langlands.Representation.RankinSelberg.ComponentGammaProductStatement
import Langlands.Representation.RankinSelberg.ComponentFactorComparisonProof

/-! Gamma multiplicativity transferred to actual full-Whittaker-type components. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial TemperedLFactorGamma

universe uF uV uW uV₂ uW₂

/-- The actual component ratio follows from block multiplicativity and gamma
comparison, with every L-polynomial certificate supplied explicitly. -/
theorem componentGammaProduct :
    ComponentGammaProductStatement.{uF, uV, uW, uV₂, uW₂} := by
  classical
  intro p _ F ψ ν r t k l m n hm hn V _ _ W _ _ V₂ _ _ W₂ _ _
    ξ η π σ hξ hη hπ hσ hc hd P PD Q QD hP hQ hPD hQD
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have hξind := normalizedProductWhittakerType p F ψ r k m hm ξ hξ
  have hηind := normalizedProductWhittakerType p F ψ t l n hn η hη
  obtain ⟨e₀, he₀⟩ := epsilon_exists_of_whittakerType F ψ ν π σ hπ hσ
  have he : ∀ i j, ∃ e : ℂˣ × ℤ,
      IsPadicSymmetricEpsilonFactor F ψ ν.val (ξ i) (η j) e :=
    fun i j => epsilon_exists_of_whittakerType F ψ ν (ξ i) (η j) (hξ i) (hη j)
  choose e he using he
  obtain ⟨G, hG, hGind⟩ := gamma_doubleProduct F ψ ν m n hm hn ξ η hξ hη
  have hblock (i j) : G i j =
      rationalGammaExpression (LocalFactor.residueReflection F)
        (e i j).1 (e i j).2 (Q i j) (QD i j) :=
    (symmetricGammaExpression p F ψ ν (m i) (n j) (ξ i) (η j)
      (whittakerTypeGammaConstructionInput p F ψ ν (m i) (n j)
        (V i) (W j) (ξ i) (η j) (hξ i) (hη j))
      (e i j) (Q i j) (QD i j) (he i j) (hQ i j) (hQD i j) (G i j)).mp (hG i j)
  have hGcomponent : IsPadicSymmetricGammaFactor F ψ ν.val π σ
      (rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2 P PD) :=
    (symmetricGammaExpression p F ψ ν r t π σ
      (whittakerTypeGammaConstructionInput p F ψ ν r t V₂ W₂ π σ hπ hσ)
      e₀ P PD he₀ hP hPD _).mpr rfl
  have hind : (∏ i, ∏ j, G i j) =
      rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2 P PD :=
    ((componentFactorComparison p F ψ ν.val r t π σ _ _
      hξind.1.1 hηind.1.1 hc hd).1 _ _ hGcomponent hGind).symm
  have hprod :
      rationalGammaExpression (LocalFactor.residueReflection F)
        (∏ i, ∏ j, (e i j).1) (∑ i, ∑ j, (e i j).2)
        (∏ i, ∏ j, Q i j) (∏ i, ∏ j, QD i j) =
      rationalGammaExpression (LocalFactor.residueReflection F) e₀.1 e₀.2 P PD := by
    rw [rationalGammaExpression_prod]
    simp_rw [rationalGammaExpression_prod, ← hblock]
    exact hind
  exact ⟨{
    coefficient := e₀.1 / (∏ i, ∏ j, (e i j).1)
    exponent := e₀.2 - (∑ i, ∑ j, (e i j).2)
    ratio := reflectedRatio_of_gammaExpression_eq _ _ _ _ _ _ _ _ _ hprod }⟩

end Langlands.RankinSelberg
