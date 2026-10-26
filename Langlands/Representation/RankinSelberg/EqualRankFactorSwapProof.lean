import Langlands.Representation.RankinSelberg.EqualRankFactorSwapStatement
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.Representation.RankinSelberg.CharacterChangeMeasure
import Langlands.Representation.RankinSelberg.EqualRankSwapFactors

/-! Equal-rank L exchange by inverse-character commutation and character transport. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

section Commutation

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

private theorem equalRankZetaValues_swap_subset
    (q : ℕ) (ψ χ : UnitaryAdditiveCharacter F)
    (hχ : standardCharacter χ n = inverseStandardCharacter ψ n)
    (hχ' : inverseStandardCharacter χ n = standardCharacter ψ n)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    equalRankZetaValues q ψ abv μ π σ ⊆ equalRankZetaValues q χ abv μ σ π := by
  rintro R ⟨f, hf, f', hf', Φ, hc, hR⟩
  let g : WhittakerFunctions χ n :=
    ⟨f'.val, by
      simpa only [WhittakerFunctions, InverseWhittakerFunctions, hχ] using f'.property⟩
  let g' : InverseWhittakerFunctions χ n :=
    ⟨f.val, by
      simpa only [WhittakerFunctions, InverseWhittakerFunctions, hχ'] using f.property⟩
  have hg : g ∈ whittakerSet χ n σ := by
    obtain ⟨ℓ', v', hv'⟩ := hf'
    let ℓ : glFunctionals χ n σ := ⟨ℓ'.val, by
      simpa only [glFunctionals, glInverseFunctionals, hχ] using ℓ'.property⟩
    refine ⟨ℓ, v', ?_⟩
    apply Subtype.ext
    exact congrArg (fun w : InverseWhittakerFunctions ψ n => w.val) hv'
  have hg' : g' ∈ inverseWhittakerSet χ n π := by
    obtain ⟨ℓ, v, hv⟩ := hf
    let ℓ' : glInverseFunctionals χ n π := ⟨ℓ.val, by
      simpa only [glFunctionals, glInverseFunctionals, hχ'] using ℓ.property⟩
    refine ⟨ℓ', v, ?_⟩
    apply Subtype.ext
    exact congrArg (fun w : WhittakerFunctions ψ n => w.val) hv
  have hI (s : ℂ) : equalRankIntegrand χ abv g g' Φ s =
      equalRankIntegrand ψ abv f f' Φ s := by
    funext x
    induction x using Quotient.inductionOn with
    | h a =>
      simp only [equalRankIntegrand_mk, g, g']
      rw [mul_comm (f'.val a) (f.val a)]
  refine ⟨g, hg, g', hg', Φ, ?_, ?_⟩
  · simpa only [EqualRankConverges, hI] using hc
  · have hi : equalRankIntegral χ abv μ g g' Φ =
        equalRankIntegral ψ abv μ f f' Φ := by
      funext s
      simp only [equalRankIntegral, hI]
    rw [hi]
    exact hR

/-- Interchanging coefficient functions changes the additive character to its
inverse. The convergence and rational-continuation witnesses are retained. -/
theorem equalRankZetaValues_swap_inverse
    [IsTopologicalRing F] (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    equalRankZetaValues q ψ abv μ π σ =
      equalRankZetaValues q (ψ.scale (-1)) abv μ σ π := by
  apply Set.Subset.antisymm
  · exact equalRankZetaValues_swap_subset q ψ (ψ.scale (-1))
      (standardCharacter_scale_neg_one ψ n) (inverseStandardCharacter_scale_neg_one ψ n)
      abv μ π σ
  · exact equalRankZetaValues_swap_subset q (ψ.scale (-1)) ψ
      (inverseStandardCharacter_scale_neg_one ψ n).symm
      (standardCharacter_scale_neg_one ψ n).symm abv μ σ π

/-- The normalized polynomial is retained when exchanging the pair and
inverting the additive character. -/
theorem isEqualRankLPolynomial_swap_inverse
    [IsTopologicalRing F] (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (P : ℂ[X]) :
    IsEqualRankLPolynomial q ψ abv μ π σ P ↔
      IsEqualRankLPolynomial q (ψ.scale (-1)) abv μ σ π P := by
  unfold IsEqualRankLPolynomial
  rw [equalRankZetaValues_swap_inverse q ψ abv μ π σ]

end Commutation

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- Equal-rank p-adic L certificates are preserved at the same character and
the same supplied additive Haar measure. No factor existence is required. -/
theorem isPadicPairLPolynomial_swap_equalRank
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W) (P : ℂ[X]) :
    IsPadicPairLPolynomial F ψ ν π σ P ↔
      IsPadicPairLPolynomial F ψ ν σ π P := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun μ => ?_)
  refine imp_congr_right fun hμ => ?_
  rw [isPairLPolynomial_self, isPairLPolynomial_self]
  have hLaw := characterChangeCompatibleMeasure p F F.canonicalTopologicalData n (-1) μ hμ
  exact (isEqualRankLPolynomial_swap_inverse
    F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ P).trans
    (isEqualRankLPolynomial_characterChange_normalized F.canonicalTopologicalData n
      ψ (-1) μ hLaw W V σ π P).symm

end Padic

/-- Equal-rank exchange of all three certificates at the original additive
character and supplied self-dual Haar measure. -/
theorem equalRankFactorSwap : EqualRankFactorSwapStatement.{uF, uV, uW} := by
  intro p hp F ψ ν n V hV hMV W hW hMW π σ hπ hσ
  exact ⟨fun P => isPadicPairLPolynomial_swap_equalRank F ψ ν.val π σ P,
    (fun e => isPadicPairEpsilonFactor_swap_equalRank F ψ ν.val π σ hπ hσ e),
    fun G => isPadicPairGammaFactor_swap_equalRank F ψ ν.val π σ hπ hσ G⟩

end Langlands.RankinSelberg
