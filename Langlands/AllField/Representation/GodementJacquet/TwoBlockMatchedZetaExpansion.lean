import Langlands.Representation.GodementJacquet.TwoBlockMatchedZetaExpansion
import Langlands.AllField.Representation.GodementJacquet.InverseTransposeMatrixIntegral
import Langlands.AllField.Representation.GodementJacquet.TwoBlockDualParabolicIntegral
import Langlands.AllField.Representation.GodementJacquet.TwoBlockFunctionalEquationAssembly
import Langlands.AllField.Representation.GodementJacquet.TwoBlockZetaExpansion
/-!
# Matched expansion of two-block induced zeta integrals and their transforms

Godement–Jacquet 1972, proof of Theorem 3.4 (printed pages 37–42), for two blocks:
the shifted matrix zeta integral of a bi-smooth coefficient `f` of the normalized
induced representation is a finite sum of products of block zeta integrals, and,
with the same finite data, the zeta integral of the full Fourier transform of the
test against the inverse-transpose transform of `f` is the corresponding sum of
products of the block zeta integrals of the Fourier transforms of the block tests
against the inverse-transpose transforms of the block coefficients. This proves
`TwoBlockMatchedZetaExpansionStatement`. See the paired Markdown.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet.TwoBlock hiding blockAbs blockAbs_pos continuous_determinantWeight' continuous_leviCoefficientWeight determinantWeight_mul_of_mem determinantWeight_sub_natCast_mul_pow dual_levi_weight_identity exists_matched_zeta_expansion_of_kernel exists_twoBlock_matched_zeta_expansion exists_twoBlock_zeta_expansion exists_zeta_expansion_of_kernel glSecondCountable halfModulus halfModulus_eq instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceCarrier_2 instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_2 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_2 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyCarrier_2 instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrable_leviCoefficientWeight integrable_mul_left_radical_iff integral_leviCoefficientWeight integral_mul_left_radical integral_testFunction_parabolicPoint leviCoefficientWeight leviCoefficientWeight_mul levi_weight_identity map_mul_left_radical matchedExpansionBorel matchedExpansionGLBorel matchedExpansionGLMeasurableSpace matchedExpansionLocalField matchedExpansionMeasurableSpace matchedExpansionSecondCountable matchedExpansionT2 matchedExpansionTopology matchedExpansionTotallyDisconnected matchedExpansionValuativeRel matrixLocallyCompact matrixSecondCountable measurableEmbedding_mul_left_radical measurable_parabolicPoint measurePreserving_parabolicShift normalizedAbs_det_eq_one_of_mem padic_matrixIntegral_smul parabolicMeasure parabolicMeasure_isFiniteMeasureOnCompacts parabolicMeasure_isOpenPosMeasure parabolicMeasure_preimage_ne_top parabolicMeasure_preimage_ne_zero parabolicMeasure_sigmaFinite parabolicPoint_translation radicalWeight twoBlock_forward_generatorInputs
open Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet hiding TwoBlockMatchedZetaExpansionStatement TwoBlockMatrixAnalyticInductionStatement TwoBlockMatrixFunctionalEquationInductionStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant twoBlockMatchedZetaExpansion twoBlockMatrixFunctionalEquationInduction_of_expansion
open Langlands.AllField.GodementJacquet

open Langlands.GeneralLinear
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankContinuedForms isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Weights

end Weights

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

-- Named, so that the auto-generated names cannot clash with the anonymous local
-- instances of other modules in this namespace (e.g. `TwoBlockReverseRealization`).
local instance matchedExpansionT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance matchedExpansionSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance matchedExpansionMeasurableSpace : MeasurableSpace F := borel _
local instance matchedExpansionBorel : BorelSpace F := ⟨rfl⟩
local instance matchedExpansionTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matchedExpansionGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance matchedExpansionGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

attribute [local instance] glSecondCountable matrixLocallyCompact matrixSecondCountable
  glLocallyCompact

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- **Transformed Levi weight identity.** In parabolic coordinates, the determinant
weight with exponent `-(s + t/2)` times `δ_P^(1/2)` is the product of the block
weights with exponents `-(s + m₀/2)` and `-(s + m₁/2) - n₀`. -/
theorem dual_levi_weight_identity (L : (succBlockShape m h).Levi F)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (parabolicPoint h (L, x)) (-(s + jpssShift t)) * halfModulus F h L =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (L 0)
          (-(s + jpssShift (m 0))) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (L 1)
          (-(s + jpssShift (m 1)) - ((m 0 + 1 : ℕ) : ℂ)) := by
  have hA := blockAbs_pos F h L 0
  have hD := blockAbs_pos F h L 1
  have hw := dual_weight_identity (TwoBlockJacquet.blockRanks_add h) hA hD s
  simp only [determinantWeight, det_parabolicPoint, map_mul, halfModulus_eq, jpssShift]
  exact hw

/-- Lowering the exponent by `k` and multiplying by `|det g|^k` restores the weight. -/
theorem determinantWeight_sub_natCast_mul_pow {n : ℕ} (g : Langlands.GeneralLinear n F)
    (w : ℂ) (k : ℕ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (w - (k : ℂ)) *
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) g.val.det : ℂ) ^ k =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g w := by
  have hne : (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) g.val.det : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).ne_zero g.det_ne_zero)
  unfold determinantWeight
  rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne, sub_add_cancel]

section Expansion

/-- **Matched abstract two-block zeta expansion.** In the setting of
`exists_zeta_expansion_of_kernel`, with the radical measure taken to be the
rectangular product of a measure `ν` self-dual for `ψ`, one finite family of
weights, block tests and coefficient indices expands both the zeta integral of
the coefficient `f g = ∫ k, Γ k (k g) dμK` against `Φ`, and the zeta integral of the
inverse-transpose transform `ι f` against the full Fourier transform of `Φ`; in
the second expansion the block tests are replaced by their Fourier transforms and
the block coefficients by their inverse-transpose transforms. Each identity holds
whenever the corresponding block integrals converge. -/
theorem exists_matched_zeta_expansion_of_kernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (K : OpenSubgroup (Langlands.GeneralLinear (t + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F)))
    (hPK : ∀ g : Langlands.GeneralLinear (t + 1) F,
      ∃ (q : (succBlockShape m h).parabolic F) (k : K),
        g = (q : Langlands.GeneralLinear (t + 1) F) *
          (k : Langlands.GeneralLinear (t + 1) F))
    [MeasurableSpace K] [BorelSpace K] (μK : Measure K) [IsFiniteMeasure μK]
    (Γ : K → Langlands.GeneralLinear (t + 1) F → ℂ)
    (hΓ : Continuous fun z : K × Langlands.GeneralLinear (t + 1) F => Γ z.1 z.2)
    {N : ℕ} (φ : Fin N → SchwartzBruhat (K × K))
    (c₀ : Fin N → Langlands.GeneralLinear (m 0 + 1) F → ℂ)
    (c₁ : Fin N → Langlands.GeneralLinear (m 1 + 1) F → ℂ)
    (hc₀ : ∀ j, Continuous (c₀ j)) (hc₁ : ∀ j, Continuous (c₁ j))
    (hexp : ∀ (k k' : K) (L : (succBlockShape m h).Levi F)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F),
      Γ k (parabolicPoint h (L, x) * k') =
        halfModulus F h L * ∑ j, φ j (k, k') * (c₀ j (L 0) * c₁ j (L 1)))
    (Φ : MatrixTestFunction t F) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℂ) (Ψ₀ : ι → MatrixTestFunction (m 0) F)
      (Ψ₁ : ι → MatrixTestFunction (m 1) F) (jj : ι → Fin N),
      (∀ s : ℂ,
        (∀ j (α : MatrixTestFunction (m 0) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) (c₀ j)) →
        (∀ j (α : MatrixTestFunction (m 1) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) (c₁ j)) →
        Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift t)
            (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK) =
          ∑ i, w i * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ i) (s + jpssShift (m 0)) (c₀ (jj i)) *
            Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ i) (s + jpssShift (m 1)) (c₁ (jj i)))) ∧
      (∀ s : ℂ,
        (∀ j (α : MatrixTestFunction (m 0) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) (coefficientIota (c₀ j))) →
        (∀ j (α : MatrixTestFunction (m 1) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) (coefficientIota (c₁ j))) →
        Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ)
            (s + jpssShift t)
            (coefficientIota
              (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK)) =
          ∑ i, w i * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F
              (rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ₀ i))
              (s + jpssShift (m 0)) (coefficientIota (c₀ (jj i))) *
            Langlands.AllField.GodementJacquet.Padic.matrixIntegral F
              (rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ₁ i))
              (s + jpssShift (m 1)) (coefficientIota (c₁ (jj i))))) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SigmaFinite ν.measure := selfDualSigmaFinite F ψ ν hsd
  set μ := generalLinearHaar F t with hμ
  set dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    rectangularMeasure ν (m 0 + 1) (m 1 + 1) with hdx
  have : dx.IsAddHaarMeasure := by
    rw [hdx]
    infer_instance
  set ρ := parabolicMeasure F h dx with hρ
  have hemb : MeasurableEmbedding (Subtype.val : K → Langlands.GeneralLinear (t + 1) F) :=
    K.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  set ν' : Measure K := μ.comap Subtype.val with hν'def
  have hν' : ν'.map Subtype.val =
      μ.restrict (K : Set (Langlands.GeneralLinear (t + 1) F)) := by
    rw [hemb.map_comap, Subtype.range_coe]
  have : IsFiniteMeasure ν' := ⟨by
    rw [hemb.comap_apply, Set.image_univ, Subtype.range_coe]
    exact hK.measure_lt_top⟩
  -- translates of `Φ` along `K × K`
  obtain ⟨Lc, χ, r, hχ⟩ := exists_matrixTranslate_expansion Φ
    (fun z : K × K => ((z.1 : Langlands.GeneralLinear (t + 1) F))⁻¹)
    (fun z : K × K => (z.2 : Langlands.GeneralLinear (t + 1) F))
    (continuous_subtype_val.comp continuous_fst).inv (continuous_subtype_val.comp continuous_snd)
  set Φl : Fin Lc → MatrixTestFunction t F := fun l =>
    matrixTranslate Φ ((r l).1 : Langlands.GeneralLinear (t + 1) F)⁻¹
      ((r l).2 : Langlands.GeneralLinear (t + 1) F) with hΦl
  have hΦP := fun l => exists_upperBlockIntegral_expansion h (Φl l) dx
  choose R Ψ₀ Ψ₁ hΨ using hΦP
  set C : ℝ := (ρ (parabolicPoint h ⁻¹'
    (K : Set (Langlands.GeneralLinear (t + 1) F)))).toReal with hC
  set W : Fin Lc → Fin N → ℂ := fun l j => ∫ z, χ l z * φ j z ∂(μK.prod ν') with hW
  have hK2 : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology
      (K : Set (Langlands.GeneralLinear (t + 1) F))
  set ψK : Fin Lc × Fin N → K → K → ℂ := fun lj k k' => χ lj.1 (k, k') * φ lj.2 (k, k')
    with hψdef
  have hψ : ∀ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)),
      Integrable (fun z : K × K => ψK lj z.1 z.2) (μK.prod ν') := by
    intro lj _
    exact ((χ lj.1).continuous.mul (φ lj.2).continuous).integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have hψval : ∀ l j, ∫ z, ψK (l, j) z.1 z.2 ∂(μK.prod ν') = W l j := fun l j => rfl
  have hCeq : (ρ (parabolicPoint h ⁻¹'
      ((K.toSubgroup : Subgroup (Langlands.GeneralLinear (t + 1) F)) :
        Set (Langlands.GeneralLinear (t + 1) F)))).toReal = C := rfl
  refine ⟨Σ l : Fin Lc, Fin (R l) × Fin N, inferInstance,
    fun i => ((C⁻¹ : ℝ) : ℂ) * W i.1 i.2.2, fun i => Ψ₀ i.1 i.2.1, fun i => Ψ₁ i.1 i.2.1,
    fun i => i.2.2, ?_, ?_⟩
  · ----------------------------------------------------------------------------------
    -- the original integral
    intro s h₀ h₁
    set H : Langlands.GeneralLinear (t + 1) F → ℂ := fun g =>
      Φ g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (s + jpssShift t) with hH
    set U : Fin N → (succBlockShape m h).Levi F → ℂ := fun j =>
      leviCoefficientWeight F h (c₀ j) (c₁ j) s with hU
    set Q : Fin Lc × Fin N → (succBlockShape m h).Levi F ×
        Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ := fun lj z =>
      Φl lj.1 (parabolicPoint h z).val * U lj.2 z.1 with hQdef
    have hHc : Continuous H :=
      (Φ.continuous.comp Units.continuous_val).mul (continuous_determinantWeight' F t _)
    have hm : AEStronglyMeasurable (fun z : K × Langlands.GeneralLinear (t + 1) F =>
        H ((z.1 : Langlands.GeneralLinear (t + 1) F)⁻¹ * z.2) * Γ z.1 z.2)
        (μK.prod μ) :=
      ((hHc.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd)).mul
        hΓ).aestronglyMeasurable
    have hPstep (lj : Fin Lc × Fin N) := integral_testFunction_parabolicPoint F h dx (Φl lj.1)
      (U lj.2) (continuous_leviCoefficientWeight F h (c₀ lj.2) (c₁ lj.2) s (hc₀ lj.2)
        (hc₁ lj.2)).aestronglyMeasurable
      (integrable_leviCoefficientWeight F h (c₀ lj.2) (c₁ lj.2) s (h₀ lj.2) (h₁ lj.2))
    have hQ : ∀ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)), Integrable (Q lj) ρ :=
      fun lj _ => (hPstep lj).1
    have hexp' : ∀ (k k' : K) (z : (succBlockShape m h).Levi F ×
        Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F),
        H ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ *
            (parabolicPoint h z * (k' : Langlands.GeneralLinear (t + 1) F))) *
          Γ k (parabolicPoint h z * (k' : Langlands.GeneralLinear (t + 1) F)) =
        ∑ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)), ψK lj k k' * Q lj z := by
      rintro k k' ⟨L, x⟩
      have h1 : Φ ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ *
          (parabolicPoint h (L, x) * (k' : Langlands.GeneralLinear (t + 1) F))).val =
          ∑ l, χ l (k, k') * Φl l (parabolicPoint h (L, x)).val := by
        rw [Units.val_mul, Units.val_mul, ← Matrix.mul_assoc]
        exact hχ (k, k') (parabolicPoint h (L, x)).val
      have h2 : determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ *
            (parabolicPoint h (L, x) * (k' : Langlands.GeneralLinear (t + 1) F)))
            (s + jpssShift t) =
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (parabolicPoint h (L, 0)) (s + jpssShift t) := by
        rw [← mul_assoc, determinantWeight_mul_of_mem F K.toSubgroup hK k.property k'.property]
        simp only [determinantWeight, det_parabolicPoint]
      simp only [hH, hQdef, hψdef, hU, leviCoefficientWeight]
      rw [h1, h2, hexp k k' L x, Fintype.sum_prod_type]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      ring
    obtain ⟨-, hval⟩ := CompactFactorization.integrable_integral_coefficient_of_expansion μ
      K.toSubgroup K.isOpen.measurableSet ρ (parabolicPoint h) (measurable_parabolicPoint F h)
      (exists_parabolicPoint_mul h K.toSubgroup hPK) (parabolicPoint_translation F h dx)
      (parabolicMeasure_preimage_ne_zero F h dx K)
      (parabolicMeasure_preimage_ne_top F h dx K.toSubgroup hK)
      μK Subtype.val continuous_subtype_val.measurable ν' Subtype.val
      continuous_subtype_val.measurable hν' H Γ hm Finset.univ ψK Q hψ hQ hexp'
    have hfun : GodementJacquet.matrixIntegrand
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Φ (s + jpssShift t)
        (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK) =
        fun g => H g * ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK := by
      funext g
      simp only [GodementJacquet.matrixIntegrand, hH]
      ring
    change ∫ g, GodementJacquet.matrixIntegrand _ Φ (s + jpssShift t) _ g ∂μ = _
    rw [hfun, hval]
    have hQval : ∀ l j, ∫ z, Q (l, j) z ∂ρ =
        ∑ r, Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ l r) (s + jpssShift (m 0)) (c₀ j) *
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ l r) (s + jpssShift (m 1)) (c₁ j) := by
      intro l j
      rw [(hPstep (l, j)).2]
      exact integral_leviCoefficientWeight F h (c₀ j) (c₁ j) s (Ψ₀ l) (Ψ₁ l) (h₀ j) (h₁ j) _
        (fun L => hΨ l _ _)
    rw [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hQval l j, hψval l j, Finset.mul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Complex.real_smul, hCeq]
    ring
  · ----------------------------------------------------------------------------------
    -- the transformed integral
    intro s h₀ h₁
    set FΦ := rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ with hFΦ
    set FΦl : Fin Lc → MatrixTestFunction t F := fun l =>
      rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd (Φl l) with hFΦl
    set H : Langlands.GeneralLinear (t + 1) F → ℂ := fun g =>
      FΦ (GeneralLinear.inverseTranspose (t + 1) F g).val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
          (-(s + jpssShift t)) with hH
    set u₀ : Fin N → Langlands.GeneralLinear (m 0 + 1) F → ℂ := fun j a =>
      c₀ j a * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) a
        (-(s + jpssShift (m 0))) with hu₀def
    set u₁ : Fin N → Langlands.GeneralLinear (m 1 + 1) F → ℂ := fun j d =>
      c₁ j d * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) d
        (-(s + jpssShift (m 1)) - ((m 0 + 1 : ℕ) : ℂ)) with hu₁def
    set Q : Fin Lc × Fin N → (succBlockShape m h).Levi F ×
        Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ := fun lj z =>
      FΦl lj.1 (GeneralLinear.inverseTranspose (t + 1) F (parabolicPoint h z)).val *
        (u₀ lj.2 (z.1 0) * u₁ lj.2 (z.1 1)) with hQdef
    have hθc : ∀ n : ℕ, Continuous fun g : Langlands.GeneralLinear n F =>
        (GeneralLinear.inverseTranspose n F g).val := fun n =>
      Units.continuous_val.comp (GeneralLinear.continuous_inverseTranspose n F)
    have hHc : Continuous H :=
      (FΦ.continuous.comp (hθc (t + 1))).mul (continuous_determinantWeight' F t _)
    have hm : AEStronglyMeasurable (fun z : K × Langlands.GeneralLinear (t + 1) F =>
        H ((z.1 : Langlands.GeneralLinear (t + 1) F)⁻¹ * z.2) * Γ z.1 z.2)
        (μK.prod μ) :=
      ((hHc.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd)).mul
        hΓ).aestronglyMeasurable
    -- block integrability from transformed block convergence
    have hθ0 := Langlands.AllField.GodementJacquet.Padic.generalLinearHaar_measurePreserving_inverseTranspose F (m 0)
    have hθ1 := Langlands.AllField.GodementJacquet.Padic.generalLinearHaar_measurePreserving_inverseTranspose F (m 1)
    have hθt := Langlands.AllField.GodementJacquet.Padic.generalLinearHaar_measurePreserving_inverseTranspose F t
    have hu₀m : ∀ j, AEStronglyMeasurable (u₀ j) (generalLinearHaar F (m 0)) :=
      fun j => ((hc₀ j).mul (continuous_determinantWeight' F (m 0) _)).aestronglyMeasurable
    have hu₁m : ∀ j, AEStronglyMeasurable (u₁ j) (generalLinearHaar F (m 1)) :=
      fun j => ((hc₁ j).mul (continuous_determinantWeight' F (m 1) _)).aestronglyMeasurable
    have hint₀ : ∀ j (Ψ : MatrixTestFunction (m 0) F),
        (fun a => Ψ (GeneralLinear.inverseTranspose (m 0 + 1) F a).val * u₀ j a) =
          inverseTransposeSubstitutedIntegrand
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Ψ (s + jpssShift (m 0))
            (c₀ j) := by
      intro j Ψ
      funext a
      simp only [inverseTransposeSubstitutedIntegrand, hu₀def]
      ring
    have hint₁ : ∀ j (Ψ : MatrixTestFunction (m 1) F),
        (fun d => Ψ (GeneralLinear.inverseTranspose (m 1 + 1) F d).val *
          (u₁ j d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^
            (m 0 + 1))) =
          inverseTransposeSubstitutedIntegrand
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Ψ (s + jpssShift (m 1))
            (c₁ j) := by
      intro j Ψ
      funext d
      simp only [inverseTransposeSubstitutedIntegrand, hu₁def]
      rw [mul_assoc (c₁ j d), determinantWeight_sub_natCast_mul_pow]
      ring
    have hu₀ : ∀ j (Ψ : MatrixTestFunction (m 0) F),
        Integrable
          (fun a => Ψ (GeneralLinear.inverseTranspose (m 0 + 1) F a).val * u₀ j a)
          (generalLinearHaar F (m 0)) := by
      intro j Ψ
      rw [hint₀ j Ψ]
      exact (matrixConverges_coefficientIota_iff _ hθ0 Ψ _ (c₀ j)).mp (h₀ j Ψ)
    have hu₁ : ∀ j (Ψ : MatrixTestFunction (m 1) F),
        Integrable
          (fun d => Ψ (GeneralLinear.inverseTranspose (m 1 + 1) F d).val *
            (u₁ j d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^
              (m 0 + 1)))
          (generalLinearHaar F (m 1)) := by
      intro j Ψ
      rw [hint₁ j Ψ]
      exact (matrixConverges_coefficientIota_iff _ hθ1 Ψ _ (c₁ j)).mp (h₁ j Ψ)
    -- the lower-left partial integrals of the transformed translates
    have hpart : ∀ l x y, ∫ C, FΦl l (blockMatrix (blockEquiv h) x 0 C y)
        ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1) =
        ∑ k ∈ Finset.univ, rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ₀ l k) x *
          rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ₁ l k) y := by
      intro l x y
      simp only [hFΦl, rectangularFourierEquiv_apply]
      exact integral_rectangularFourierIntegral_blockMatrix_lowerLeft_of_tensor ψ ν
        (blockEquiv h) hsd (Φl l) Finset.univ (Ψ₀ l) (Ψ₁ l) (fun A D => hΨ l A D) x y
    have hPstep (lj : Fin Lc × Fin N) := Langlands.AllField.GodementJacquet.Padic.integrable_integral_dualParabolic_levi F
      (blockEquiv h) ν (fun i : Fin 2 => generalLinearHaar F (m i))
      (parabolicPoint h) (parabolicPoint_val h) (FΦl lj.1) (hu₀m lj.2) (hu₁m lj.2)
      (hu₀ lj.2) (hu₁ lj.2) Finset.univ
      (fun k => rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ₀ lj.1 k))
      (fun k => rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ₁ lj.1 k))
      (hpart lj.1)
    have hQ : ∀ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)), Integrable (Q lj) ρ :=
      fun lj _ => (hPstep lj).1
    have hexp' : ∀ (k k' : K) (z : (succBlockShape m h).Levi F ×
        Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F),
        H ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ *
            (parabolicPoint h z * (k' : Langlands.GeneralLinear (t + 1) F))) *
          Γ k (parabolicPoint h z * (k' : Langlands.GeneralLinear (t + 1) F)) =
        ∑ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)), ψK lj k k' * Q lj z := by
      rintro k k' ⟨L, x⟩
      have h1 : FΦ (GeneralLinear.inverseTranspose (t + 1) F
          ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ *
            (parabolicPoint h (L, x) * (k' : Langlands.GeneralLinear (t + 1) F)))).val =
          ∑ l, χ l (k, k') * FΦl l
            (GeneralLinear.inverseTranspose (t + 1) F (parabolicPoint h (L, x))).val :=
        Langlands.AllField.GodementJacquet.Padic.rectangularFourierEquiv_inverseTranspose_translate_of_mem F ψ ν hsd K.toSubgroup hK
          (K.toSubgroup.inv_mem k.property) k'.property Φ Finset.univ (fun l => χ l (k, k')) Φl
          (fun X => hχ (k, k') X) (parabolicPoint h (L, x))
      have h2 : determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ *
            (parabolicPoint h (L, x) * (k' : Langlands.GeneralLinear (t + 1) F)))
            (-(s + jpssShift t)) =
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (parabolicPoint h (L, x)) (-(s + jpssShift t)) := by
        rw [← mul_assoc, determinantWeight_mul_of_mem F K.toSubgroup hK k.property k'.property]
      have h3 := dual_levi_weight_identity F h L x s
      simp only [hH, hQdef, hψdef, hu₀def, hu₁def]
      rw [h1, h2, hexp k k' L x, Fintype.sum_prod_type]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      linear_combination (χ l (k, k') * φ j (k, k') *
        FΦl l (GeneralLinear.inverseTranspose (t + 1) F (parabolicPoint h (L, x))).val *
        c₀ j (L 0) * c₁ j (L 1)) * h3
    obtain ⟨-, hval⟩ := CompactFactorization.integrable_integral_coefficient_of_expansion μ
      K.toSubgroup K.isOpen.measurableSet ρ (parabolicPoint h) (measurable_parabolicPoint F h)
      (exists_parabolicPoint_mul h K.toSubgroup hPK) (parabolicPoint_translation F h dx)
      (parabolicMeasure_preimage_ne_zero F h dx K)
      (parabolicMeasure_preimage_ne_top F h dx K.toSubgroup hK)
      μK Subtype.val continuous_subtype_val.measurable ν' Subtype.val
      continuous_subtype_val.measurable hν' H Γ hm Finset.univ ψK Q hψ hQ hexp'
    have hfun : inverseTransposeSubstitutedIntegrand
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) FΦ (s + jpssShift t)
        (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK) =
        fun g => H g * ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK := by
      funext g
      simp only [inverseTransposeSubstitutedIntegrand, hH]
      ring
    change GodementJacquet.matrixIntegral _ μ FΦ (s + jpssShift t) _ = _
    rw [matrixIntegral_coefficientIota _ hθt, hfun, hval]
    have hblock₀ : ∀ j (Ψ : MatrixTestFunction (m 0) F),
        ∫ a, Ψ (GeneralLinear.inverseTranspose (m 0 + 1) F a).val * u₀ j a
            ∂generalLinearHaar F (m 0) =
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Ψ (s + jpssShift (m 0)) (coefficientIota (c₀ j)) := by
      intro j Ψ
      rw [hint₀ j Ψ]
      exact (matrixIntegral_coefficientIota _ hθ0 Ψ _ (c₀ j)).symm
    have hblock₁ : ∀ j (Ψ : MatrixTestFunction (m 1) F),
        ∫ d, Ψ (GeneralLinear.inverseTranspose (m 1 + 1) F d).val *
            (u₁ j d * (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) d.val.det : ℂ) ^
              (m 0 + 1)) ∂generalLinearHaar F (m 1) =
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Ψ (s + jpssShift (m 1)) (coefficientIota (c₁ j)) := by
      intro j Ψ
      rw [hint₁ j Ψ]
      exact (matrixIntegral_coefficientIota _ hθ1 Ψ _ (c₁ j)).symm
    have hQval : ∀ l j, ∫ z, Q (l, j) z ∂ρ =
        ∑ r, Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd
            (Ψ₀ l r)) (s + jpssShift (m 0)) (coefficientIota (c₀ j)) *
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd
            (Ψ₁ l r)) (s + jpssShift (m 1)) (coefficientIota (c₁ j)) := by
      intro l j
      refine ((hPstep (l, j)).2).trans ?_
      exact Finset.sum_congr rfl fun r _ => by rw [hblock₀, hblock₁]
    rw [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hQval l j, hψval l j, Finset.mul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Complex.real_smul, hCeq]
    ring

end Expansion

section Forward

variable {V : Fin 2 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (V i))

/-- **Matched forward expansion.** For smooth admissible blocks, a full-matrix test
`Φ` and a coefficient `f = ⟨ℓ, I(g) v⟩` of the normalized induced representation
`I`, there are finitely many weights, block tests and actual block bi-smooth
coefficients, chosen independently of `s`, such that: whenever all block integrals
converge at `s + m₀/2` and `s + m₁/2`, the zeta integral of `f` against `Φ` at
`s + t/2` is the weighted sum of products of the block zeta integrals; and whenever
all inverse-transpose block integrals converge there, the zeta integral of `ι f`
against the full Fourier transform of `Φ` is the same weighted sum with Fourier
transformed block tests and inverse-transpose block coefficients. -/
theorem exists_twoBlock_matched_zeta_expansion (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (Φ : MatrixTestFunction t F)
    (ℓ : SmoothDual ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ))
    (v : smoothVectors ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℂ) (Ψ₀ : ι → MatrixTestFunction (m 0) F)
      (Ψ₁ : ι → MatrixTestFunction (m 1) F)
      (f₀ : ι → biSmoothMatrixCoefficients (σ 0)) (f₁ : ι → biSmoothMatrixCoefficients (σ 1)),
      (∀ s : ℂ,
        (∀ (c : biSmoothMatrixCoefficients (σ 0)) (α : MatrixTestFunction (m 0) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) c.val) →
        (∀ (c : biSmoothMatrixCoefficients (σ 1)) (α : MatrixTestFunction (m 1) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) c.val) →
        Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift t)
            (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
              ℓ v) =
          ∑ i, w i * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ i) (s + jpssShift (m 0)) (f₀ i).val *
            Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ i) (s + jpssShift (m 1)) (f₁ i).val)) ∧
      (∀ s : ℂ,
        (∀ (c : biSmoothMatrixCoefficients (σ 0)) (α : MatrixTestFunction (m 0) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) (coefficientIota c.val)) →
        (∀ (c : biSmoothMatrixCoefficients (σ 1)) (α : MatrixTestFunction (m 1) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) (coefficientIota c.val)) →
        Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (rectangularFourierEquiv ψ ν (t + 1) (t + 1) hsd Φ)
            (s + jpssShift t)
            (coefficientIota
              (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
                ℓ v)) =
          ∑ i, w i * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F
              (rectangularFourierEquiv ψ ν (m 0 + 1) (m 0 + 1) hsd (Ψ₀ i))
              (s + jpssShift (m 0)) (coefficientIota (f₀ i).val) *
            Langlands.AllField.GodementJacquet.Padic.matrixIntegral F
              (rectangularFourierEquiv ψ ν (m 1 + 1) (m 1 + 1) hsd (Ψ₁ i))
              (s + jpssShift (m 1)) (coefficientIota (f₁ i).val))) := by
  classical
  obtain ⟨K, hK, hPK, hμ⟩ := exists_compactProductCoefficientFormula (V := V)
    (⟨⟩ : LocalFieldData F) (succBlockShape m h) (Nat.succ_pos t)
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μK, _, hprob, hformula⟩ := hμ
  obtain ⟨E, hE⟩ := hformula σ hσa
  obtain ⟨N, φ, ℓ', w', hpair⟩ := exists_compactProductPairing_expansion
    (⟨⟩ : LocalFieldData F) (succBlockShape m h) σ hσa K hK (E ℓ) v.val
  -- the compact kernel
  let Γ : K → Langlands.GeneralLinear (t + 1) F → ℂ := fun k y =>
    smoothDualPairing ((succBlockShape m h).blockTensor σ)
      (Induction.eval _ _ (E ℓ) (k : Langlands.GeneralLinear (t + 1) F))
      (Induction.eval _ _ v.val y)
  have hΓ : Continuous fun z : K × Langlands.GeneralLinear (t + 1) F => Γ z.1 z.2 := by
    have hl := (Induction.eval_isLocallyConstant _ _ (E ℓ)).comp_continuous
      (continuous_subtype_val.comp (continuous_fst (X := K)
        (Y := Langlands.GeneralLinear (t + 1) F)))
    have hv := (Induction.eval_isLocallyConstant _ _ v.val).comp_continuous
      (continuous_snd (X := K) (Y := Langlands.GeneralLinear (t + 1) F))
    exact (hl.comp₂ hv fun a b =>
      smoothDualPairing ((succBlockShape m h).blockTensor σ) a b).continuous
  -- block coefficients
  let c₀ : Fin N → Langlands.GeneralLinear (m 0 + 1) F → ℂ := fun j =>
    matrixCoefficient (σ 0) (smoothDualPairing (σ 0) (ℓ' j 0)) (w' j 0)
  let c₁ : Fin N → Langlands.GeneralLinear (m 1 + 1) F → ℂ := fun j =>
    matrixCoefficient (σ 1) (smoothDualPairing (σ 1) (ℓ' j 1)) (w' j 1)
  have hc₀ : ∀ j, Continuous (c₀ j) := fun j =>
    (matrixCoefficient_isLocallyConstant (σ 0) _ _ (hσs 0 _)).continuous
  have hc₁ : ∀ j, Continuous (c₁ j) := fun j =>
    (matrixCoefficient_isLocallyConstant (σ 1) _ _ (hσs 1 _)).continuous
  have hmem₀ (j : Fin N) : c₀ j ∈ biSmoothMatrixCoefficients (σ 0) :=
    Submodule.subset_span ⟨ℓ' j 0, ⟨w' j 0, hσs 0 _⟩, rfl⟩
  have hmem₁ (j : Fin N) : c₁ j ∈ biSmoothMatrixCoefficients (σ 1) :=
    Submodule.subset_span ⟨ℓ' j 1, ⟨w' j 1, hσs 1 _⟩, rfl⟩
  -- the kernel in parabolic coordinates
  have hexp : ∀ (k k' : K) (L : (succBlockShape m h).Levi F)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F),
      Γ k (parabolicPoint h (L, x) * k') =
        halfModulus F h L * ∑ j, φ j (k, k') * (c₀ j (L 0) * c₁ j (L 1)) := by
    intro k k' L x
    have hcov := (⟨⟩ : LocalFieldData F).normalizedProductInduced_covariant
      (succBlockShape m h) σ v.val ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ k'
    have hLP : (succBlockShape m h).leviProjection F
        ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ = L :=
      congrArg Prod.fst (parabolicCoord_parabolicPoint h (L, x))
    have hk := hpair k k' L
    change smoothDualPairing ((succBlockShape m h).blockTensor σ)
      (Induction.eval _ _ (E ℓ) (k : Langlands.GeneralLinear (t + 1) F))
      (Induction.eval _ _ v.val (parabolicPoint h (L, x) * k')) = _
    rw [hcov, hLP, map_smul, smul_eq_mul]
    congr 1
    rw [show smoothDualPairing ((succBlockShape m h).blockTensor σ)
        (Induction.eval _ _ (E ℓ) (k : Langlands.GeneralLinear (t + 1) F))
        ((succBlockShape m h).blockTensor σ L (Induction.eval _ _ v.val k')) =
      compactProductPairingKernel (⟨⟩ : LocalFieldData F) (succBlockShape m h) σ (E ℓ) v.val
        k k' L from rfl, hk]
    apply Finset.sum_congr rfl
    intro j _
    rw [Fin.prod_univ_two]
  -- the coefficient is the compact integral
  have hcoef : biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
      ℓ v = fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK := by
    funext g
    exact (hE ℓ v.val g).2
  obtain ⟨ι, hι, w, Ψ₀, Ψ₁, jj, hA, hAD⟩ := exists_matched_zeta_expansion_of_kernel F h ψ ν hsd
    K hK hPK μK Γ hΓ φ c₀ c₁ hc₀ hc₁ hexp Φ
  refine ⟨ι, hι, w, Ψ₀, Ψ₁, fun i => ⟨c₀ (jj i), hmem₀ (jj i)⟩,
    fun i => ⟨c₁ (jj i), hmem₁ (jj i)⟩, fun s h₀ h₁ => ?_, fun s h₀ h₁ => ?_⟩
  · rw [hcoef]
    exact hA s (fun j α => h₀ ⟨c₀ j, hmem₀ j⟩ α) (fun j α => h₁ ⟨c₁ j, hmem₁ j⟩ α)
  · rw [hcoef]
    exact hAD s (fun j α => h₀ ⟨c₀ j, hmem₀ j⟩ α) (fun j α => h₁ ⟨c₁ j, hmem₁ j⟩ α)

end Forward

/-- Scalars pull out of the canonical p-adic matrix integral. -/
theorem padic_matrixIntegral_smul {n : ℕ} (Ψ : MatrixTestFunction n F) (s c : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) :
    Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Ψ s (c • f) = c * Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Ψ s f :=
  matrixIntegral_smul c

end Padic

end Langlands.AllField.GodementJacquet.TwoBlock

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding TwoBlockMatchedZetaExpansionStatement TwoBlockMatrixAnalyticInductionStatement TwoBlockMatrixFunctionalEquationInductionStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant twoBlockMatchedZetaExpansion twoBlockMatrixFunctionalEquationInduction_of_expansion
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankContinuedForms isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV

/-- **Matched expansion.** The internal interface `TwoBlockMatchedZetaExpansionStatement`
holds: the matched forward expansion, with the weights absorbed into the first
block coefficients, reindexed by `Fin M`, on the common convergence half-planes of
the block data. -/
theorem twoBlockMatchedZetaExpansion : TwoBlockMatchedZetaExpansionStatement.{uF, uV} := by
  intro F _ _ _ _
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  have : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro t m h V hadd hmod σ hsm had ψ ν hsd ω hω P PD c a hdata Φ ℓ v
  obtain ⟨ι, hι, w, Ψ₀, Ψ₁, f₀, f₁, hZ, hZD⟩ :=
    Langlands.AllField.GodementJacquet.TwoBlock.exists_twoBlock_matched_zeta_expansion F h σ hsm had ψ ν hsd Φ ℓ v
  obtain ⟨a₀, ha₀⟩ := (hdata 0).1.1
  obtain ⟨a₁, ha₁⟩ := (hdata 1).1.1
  obtain ⟨b₀, hb₀⟩ := (hdata 0).2.1.1
  obtain ⟨b₁, hb₁⟩ := (hdata 1).2.1.1
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => Ψ₀ (e.symm i), fun i => Ψ₁ (e.symm i),
    fun i => w (e.symm i) • f₀ (e.symm i), fun i => f₁ (e.symm i),
    ⟨max a₀ a₁, fun s hs => ?_⟩, ⟨max b₀ b₁, fun s hs => ?_⟩⟩
  · rw [hZ s (fun c α => ha₀ α c s ((le_max_left _ _).trans_lt hs))
      (fun c α => ha₁ α c s ((le_max_right _ _).trans_lt hs)), ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Langlands.AllField.GodementJacquet.TwoBlock.padic_matrixIntegral_smul, mul_assoc]
  · rw [hZD s (fun c α => hb₀ α c s ((le_max_left _ _).trans_lt hs))
      (fun c α => hb₁ α c s ((le_max_right _ _).trans_lt hs)), ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hι0 : coefficientIota ((w (e.symm i) • f₀ (e.symm i) :
        biSmoothMatrixCoefficients (σ 0)) : Langlands.GeneralLinear (m 0 + 1) F → ℂ) =
        w (e.symm i) • coefficientIota (f₀ (e.symm i)).val := rfl
    rw [hι0, Langlands.AllField.GodementJacquet.TwoBlock.padic_matrixIntegral_smul, mul_assoc]

end Langlands.AllField.GodementJacquet
