import Langlands.Representation.GodementJacquet.TwoBlockReverseRealization
import Langlands.AllField.Representation.GodementJacquet.TwoBlockZetaExpansion
/-!
# Reverse realization of products of block zeta integrals

Godement–Jacquet 1972, Theorem 3.4 (printed 43–45), for two blocks, by a direct
construction instead of Lemma 3.4.6: for block tests `Φ₀, Φ₁` and actual block
bi-smooth coefficients, a test `Φ` supported near the upper block-triangular
matrices and induced sections supported on `P K₀` realize a nonzero constant times
the product of the two block zeta integrals as an induced matrix zeta integral.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet.TwoBlock hiding blockAbs blockAbs_pos blockJoin blockJoin_blockSplit blockSplit blockSplit_upper continuous_blockJoin continuous_blockSplit continuous_determinantWeight' continuous_leviCoefficientWeight determinantWeight_mul_of_mem exists_compactOpen_biInvariant exists_twoBlock_reverse_realization exists_twoBlock_zeta_expansion exists_zeta_expansion_of_kernel glSecondCountable halfModulus halfModulus_eq instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceCarrier_2 instBorelSpaceCarrier_3 instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_2 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_3 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceCarrier_2 instMeasurableSpaceCarrier_3 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_3 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyCarrier_2 instSecondCountableTopologyCarrier_3 instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instT2SpaceCarrier_3 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 integrable_leviCoefficientWeight integrable_mul_left_radical_iff integralBox integralBoxTest integralBoxTest_apply integralBoxTest_zero integral_leviCoefficientWeight integral_mul_left_radical integral_testFunction_parabolicPoint isCompact_integralBox isOpen_integralBox isOpen_parabolicCompactSet leviCoefficientWeight leviCoefficientWeight_mul leviModulus_eq_one_of_mem levi_weight_identity map_mul_left_radical matrixLocallyCompact matrixSecondCountable measurableEmbedding_mul_left_radical measurable_parabolicPoint measurePreserving_parabolicShift normalizedAbs_det_eq_one_of_mem parabolicCompactSet parabolicMeasure parabolicMeasure_isFiniteMeasureOnCompacts parabolicMeasure_isOpenPosMeasure parabolicMeasure_preimage_ne_top parabolicMeasure_preimage_ne_zero parabolicMeasure_sigmaFinite parabolicPoint_translation radicalWeight reverseTest reverseTest_upper reverse_zeta_of_kernel twoBlock_forward_generatorInputs twoBlock_matrixGeneratorInputs twoBlock_reverse_generatorInput upperBlockIntegral_reverseTest zero_mem_integralBox
open Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet hiding compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant
open Langlands.AllField.GodementJacquet

open Langlands.GeneralLinear
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

attribute [local instance] glSecondCountable matrixLocallyCompact matrixSecondCountable
  glLocallyCompact

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The open set `P K₀` of products of an element of the upper two-block parabolic and
an element of `K₀`. -/
def parabolicCompactSet (K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F)) :
    Set (Langlands.GeneralLinear (t + 1) F) :=
  {y | ∃ (q : (succBlockShape m h).parabolic F) (l : K₀),
    y = (q : Langlands.GeneralLinear (t + 1) F) * (l : Langlands.GeneralLinear (t + 1) F)}

theorem isOpen_parabolicCompactSet (K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F)) :
    IsOpen (parabolicCompactSet F h K₀) := by
  have he : parabolicCompactSet F h K₀ = ⋃ q : (succBlockShape m h).parabolic F,
      (fun l => (q : Langlands.GeneralLinear (t + 1) F) * l) ''
        (K₀ : Set (Langlands.GeneralLinear (t + 1) F)) := by
    ext y
    simp only [parabolicCompactSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image,
      SetLike.mem_coe]
    constructor
    · rintro ⟨q, l, rfl⟩
      exact ⟨q, l, l.property, rfl⟩
    · rintro ⟨q, l, hl, rfl⟩
      exact ⟨q, ⟨l, hl⟩, rfl⟩
  rw [he]
  exact isOpen_iUnion fun q => isOpenMap_mul_left _ _ K₀.isOpen

/-- **Reverse computation for a kernel supported on `P K₀`.** Let `K₀ ≤ K` be compact open
subgroups, `ν` a finite measure on `K`, and `Γ` a continuous kernel on `K × GL_(t+1)` that
vanishes for `k ∉ P K₀` and, for `k = q l` with `q ∈ P`, `l ∈ K₀`, is the left translate
`y ↦ Γ₀ (q⁻¹ y)` of a continuous `Γ₀` supported on `P K₀` with
`Γ₀ (parabolicPoint (L, x) l) = δ_P(L)^(1/2) c₀(a) c₁(d)`. For a test `Φ` invariant on both
sides under `K₀` and an `s` at which all block tests converge against `c₀` and `c₁`, the
coefficient `g ↦ ∫ k, Γ k (k g) dν` has convergent zeta integral at `s + t/2`, equal to an
explicit constant times the Levi integral of `Φ^P`. -/
theorem reverse_zeta_of_kernel
    (K : OpenSubgroup (Langlands.GeneralLinear (t + 1) F))
    (K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F))
    (hK₀ : IsCompact (K₀ : Set (Langlands.GeneralLinear (t + 1) F)))
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (Γ : K → Langlands.GeneralLinear (t + 1) F → ℂ)
    (hΓ : Continuous fun z : K × Langlands.GeneralLinear (t + 1) F => Γ z.1 z.2)
    (Γ₀ : Langlands.GeneralLinear (t + 1) F → ℂ) (hΓ₀c : Continuous Γ₀)
    (hsupp : ∀ k : K, (k : Langlands.GeneralLinear (t + 1) F) ∉ parabolicCompactSet F h K₀ →
      ∀ y, Γ k y = 0)
    (htrans : ∀ (k : K) (q : (succBlockShape m h).parabolic F) (l : K₀),
      (k : Langlands.GeneralLinear (t + 1) F) =
        (q : Langlands.GeneralLinear (t + 1) F) * (l : Langlands.GeneralLinear (t + 1) F) →
      ∀ y, Γ k y = Γ₀ ((q : Langlands.GeneralLinear (t + 1) F)⁻¹ * y))
    (hΓ₀supp : ∀ y, y ∉ parabolicCompactSet F h K₀ → Γ₀ y = 0)
    (c₀ : Langlands.GeneralLinear (m 0 + 1) F → ℂ)
    (c₁ : Langlands.GeneralLinear (m 1 + 1) F → ℂ)
    (hc₀ : Continuous c₀) (hc₁ : Continuous c₁)
    (hΓ₀ : ∀ (L : (succBlockShape m h).Levi F)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) (l : K₀),
      Γ₀ (parabolicPoint h (L, x) * l) = halfModulus F h L * (c₀ (L 0) * c₁ (L 1)))
    (Φ : MatrixTestFunction t F)
    (hΦ : ∀ (l l' : K₀) (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F),
      Φ ((l : Langlands.GeneralLinear (t + 1) F).val * X *
        (l' : Langlands.GeneralLinear (t + 1) F).val) = Φ X)
    (s : ℂ)
    (h₀ : ∀ α : MatrixTestFunction (m 0) F,
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) c₀)
    (h₁ : ∀ α : MatrixTestFunction (m 1) F,
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) c₁) :
    Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift t)
        (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂ν) ∧
      Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift t)
          (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂ν) =
        (((ν {k : K | (k : Langlands.GeneralLinear (t + 1) F) ∈
              parabolicCompactSet F h K₀}).toReal *
            ((parabolicMeasure F h Measure.addHaar (parabolicPoint h ⁻¹'
              (K₀ : Set (Langlands.GeneralLinear (t + 1) F)))).toReal)⁻¹ *
            (generalLinearHaar F t
              (K₀ : Set (Langlands.GeneralLinear (t + 1) F))).toReal : ℝ) : ℂ) *
          ∫ L, upperBlockIntegral h Φ Measure.addHaar ((L 0).val, (L 1).val) *
            (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L)
            ∂(Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)) := by
  classical
  have hK2 : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology
      (K : Set (Langlands.GeneralLinear (t + 1) F))
  set μ := generalLinearHaar F t with hμ
  set dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) := Measure.addHaar
    with hdx
  set ρ := parabolicMeasure F h dx with hρ
  set S' := parabolicCompactSet F h K₀ with hS'def
  have hS'o : IsOpen S' := isOpen_parabolicCompactSet F h K₀
  set S : Set K := {k | (k : Langlands.GeneralLinear (t + 1) F) ∈ S'} with hSdef
  have hSm : MeasurableSet S := (hS'o.preimage continuous_subtype_val).measurableSet
  have hK₀m : MeasurableSet (K₀ : Set (Langlands.GeneralLinear (t + 1) F)) :=
    K₀.isOpen.measurableSet
  set H : Langlands.GeneralLinear (t + 1) F → ℂ := fun g =>
    Φ g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
      (s + jpssShift t) with hH
  set U := leviCoefficientWeight F h c₀ c₁ s with hU
  set Ψ₀ : Langlands.GeneralLinear (t + 1) F → ℂ := fun y => H y * Γ₀ y with hΨ₀def
  set Q : (succBlockShape m h).Levi F ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ := fun z =>
    Φ (parabolicPoint h z).val * U z.1 with hQdef
  have hHc : Continuous H :=
    (Φ.continuous.comp Units.continuous_val).mul (continuous_determinantWeight' F t _)
  -- invariance of `H` under `K₀`
  have hHleft : ∀ (l : K₀) (y : Langlands.GeneralLinear (t + 1) F),
      H ((l : Langlands.GeneralLinear (t + 1) F)⁻¹ * y) = H y := by
    intro l y
    have h1 : Φ ((l : Langlands.GeneralLinear (t + 1) F)⁻¹ * y).val = Φ y.val := by
      have := hΦ l⁻¹ 1 y.val
      simpa using this
    have h2 := determinantWeight_mul_of_mem F K₀.toSubgroup hK₀ l.property K₀.one_mem y
      (s + jpssShift t)
    rw [mul_one] at h2
    simp only [hH, h1, h2]
  have hHright : ∀ (l : K₀) (y : Langlands.GeneralLinear (t + 1) F),
      H (y * (l : Langlands.GeneralLinear (t + 1) F)) = H y := by
    intro l y
    have h1 : Φ (y * (l : Langlands.GeneralLinear (t + 1) F)).val = Φ y.val := by
      have := hΦ 1 l y.val
      simpa using this
    have h2 := determinantWeight_mul_of_mem F K₀.toSubgroup hK₀ K₀.one_mem l.property y
      (s + jpssShift t)
    rw [inv_one, one_mul] at h2
    simp only [hH, h1, h2]
  -- the parabolic reduction for `Q`
  have hUc : Continuous U := continuous_leviCoefficientWeight F h c₀ c₁ s hc₀ hc₁
  have hPs := integral_testFunction_parabolicPoint F h dx Φ U hUc.aestronglyMeasurable
    (integrable_leviCoefficientWeight F h c₀ c₁ s h₀ h₁)
  have hQeq : ∀ (z : (succBlockShape m h).Levi F ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) (l : K₀),
      Ψ₀ (parabolicPoint h z * (l : Langlands.GeneralLinear (t + 1) F)) = Q z := by
    rintro ⟨L, x⟩ l
    simp only [hΨ₀def, hQdef, hU, leviCoefficientWeight]
    rw [hHright, hΓ₀]
    simp only [hH, determinantWeight, det_parabolicPoint]
    ring
  -- integrability and integral of `Ψ₀` through the factorization over `K₀`
  have hSfac : ∀ y ∈ S', ∃ z, ∃ k₀ ∈ K₀.toSubgroup, y = parabolicPoint h z * k₀ := by
    rintro y ⟨q, l, rfl⟩
    exact ⟨parabolicCoord h q, l, l.property, by rw [parabolicPoint_parabolicCoord]⟩
  have hSK : ∀ z, ∀ k ∈ K₀.toSubgroup, parabolicPoint h z * k ∈ S' := fun z k hk =>
    ⟨⟨parabolicPoint h z, parabolicPoint_mem h z⟩, ⟨k, hk⟩, rfl⟩
  have hpos := parabolicMeasure_preimage_ne_zero F h dx K₀
  have hfin := parabolicMeasure_preimage_ne_top F h dx K₀.toSubgroup hK₀
  have hΨ₀c : Continuous Ψ₀ := hHc.mul hΓ₀c
  have hfinK₀ : IsFiniteMeasure (μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F))) :=
    isFiniteMeasure_restrict.mpr hK₀.measure_lt_top.ne
  have hcompint : Integrable (fun p : Langlands.GeneralLinear (t + 1) F ×
      ((succBlockShape m h).Levi F × Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) =>
      Ψ₀ (parabolicPoint h p.2 * p.1))
      ((μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F))).prod ρ) := by
    have h1 : Integrable (fun p : Langlands.GeneralLinear (t + 1) F ×
        ((succBlockShape m h).Levi F ×
          Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) => (1 : ℂ) * Q p.2)
        ((μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F))).prod ρ) :=
      (integrable_const (1 : ℂ)).mul_prod hPs.1
    refine h1.congr ?_
    have hae : ∀ᵐ p ∂((μ.restrict (K₀ : Set (Langlands.GeneralLinear (t + 1) F))).prod ρ),
        p.1 ∈ (K₀ : Set (Langlands.GeneralLinear (t + 1) F)) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hK₀m)
    filter_upwards [hae] with p hp
    rw [one_mul, hQeq p.2 ⟨p.1, hp⟩]
  have hS'int := (CompactFactorization.integrable_comp_mul_iff_of_subset μ K₀.toSubgroup hK₀m ρ
    (parabolicPoint h) (measurable_parabolicPoint F h) (parabolicPoint_translation F h dx) S'
    hS'o.measurableSet hSfac hSK hpos hfin hΨ₀c.aestronglyMeasurable).mp hcompint
  have hsuppΨ : Function.support Ψ₀ ⊆ S' := by
    intro y hy
    by_contra hn
    exact hy (by simp only [hΨ₀def, hΓ₀supp y hn, mul_zero])
  have hΨ₀int : Integrable Ψ₀ μ := (integrableOn_iff_integrable_of_support_subset hsuppΨ).mp hS'int
  have hval0 := CompactFactorization.integral_restrict_integral_mul_of_subset μ K₀.toSubgroup
    hK₀m ρ (parabolicPoint h) (measurable_parabolicPoint F h) (parabolicPoint_translation F h dx)
    S' hS'o.measurableSet hSfac hSK hpos hfin hS'int
  have hLHS : ∫ k in (K₀ : Set (Langlands.GeneralLinear (t + 1) F)),
      ∫ z, Ψ₀ (parabolicPoint h z * k) ∂ρ ∂μ =
        μ.real (K₀ : Set (Langlands.GeneralLinear (t + 1) F)) • ∫ z, Q z ∂ρ := by
    rw [setIntegral_congr_fun hK₀m (fun k hk => integral_congr_ae
      (Filter.Eventually.of_forall fun z => hQeq z ⟨k, hk⟩)), setIntegral_const]
  have hRHS : ∫ y in S', Ψ₀ y ∂μ = ∫ y, Ψ₀ y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp only [hΨ₀def, hΓ₀supp y hy, mul_zero]
  have hρne : (ρ (parabolicPoint h ⁻¹'
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F)))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩
  have hΨval : ∫ y, Ψ₀ y ∂μ = ((ρ (parabolicPoint h ⁻¹'
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F)))).toReal)⁻¹ •
      μ.real (K₀ : Set (Langlands.GeneralLinear (t + 1) F)) • ∫ z, Q z ∂ρ := by
    have hval0' : ∫ k in (K₀ : Set (Langlands.GeneralLinear (t + 1) F)),
        ∫ z, Ψ₀ (parabolicPoint h z * k) ∂ρ ∂μ =
          (ρ (parabolicPoint h ⁻¹' (K₀ : Set (Langlands.GeneralLinear (t + 1) F)))).toReal •
            ∫ y in S', Ψ₀ y ∂μ := hval0
    rw [← hLHS, hval0', hRHS, smul_smul, inv_mul_cancel₀ hρne, one_smul]
  -- the coefficient integral through the compact translates
  have hm : AEStronglyMeasurable (fun z : K × Langlands.GeneralLinear (t + 1) F =>
      H ((z.1 : Langlands.GeneralLinear (t + 1) F)⁻¹ * z.2) * Γ z.1 z.2) (ν.prod μ) :=
    ((hHc.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd)).mul
      hΓ).aestronglyMeasurable
  have htrans' : ∀ k ∈ S, ∃ g₀ : Langlands.GeneralLinear (t + 1) F,
      ∀ y, H ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ * y) * Γ k y = Ψ₀ (g₀ * y) := by
    rintro k ⟨q, l, hkql⟩
    refine ⟨(q : Langlands.GeneralLinear (t + 1) F)⁻¹, fun y => ?_⟩
    have e : (k : Langlands.GeneralLinear (t + 1) F)⁻¹ * y =
        (l : Langlands.GeneralLinear (t + 1) F)⁻¹ *
          ((q : Langlands.GeneralLinear (t + 1) F)⁻¹ * y) := by
      rw [hkql, mul_inv_rev, mul_assoc]
    rw [htrans k q l hkql y, e, hHleft]
  have hzero : ∀ k ∉ S, ∀ y,
      H ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ * y) * Γ k y = 0 :=
    fun k hk y => by rw [hsupp k hk y, mul_zero]
  obtain ⟨hint, hval⟩ := CompactFactorization.integrable_integral_coefficient_of_translate μ ν
    Subtype.val continuous_subtype_val.measurable H Γ hm S hSm Ψ₀ hΨ₀int htrans' hzero
  have hfun : GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      Φ (s + jpssShift t)
      (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂ν) =
      fun g => H g * ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂ν := by
    funext g
    simp only [GodementJacquet.matrixIntegrand, hH]
    ring
  refine ⟨?_, ?_⟩
  · change Integrable (GodementJacquet.matrixIntegrand _ Φ (s + jpssShift t) _) μ
    rw [hfun]
    exact hint
  · change ∫ g, GodementJacquet.matrixIntegrand _ Φ (s + jpssShift t) _ g ∂μ = _
    have hQ' : ∫ z, Q z ∂ρ = ∫ L, upperBlockIntegral h Φ Measure.addHaar ((L 0).val, (L 1).val) *
        (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L)
        ∂(Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)) := hPs.2
    rw [hfun, hval, hΨval, hQ', smul_smul, smul_smul, Complex.real_smul]
    rfl

section Tests

/-- The compact open box of integral rectangular matrices. -/
def integralBox (r s : ℕ) : Set (Matrix (Fin r) (Fin s) F) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ => ((⟨⟩ : LocalFieldData F).Integers : Set F)

theorem isCompact_integralBox (r s : ℕ) : IsCompact (integralBox F r s) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    (⟨⟩ : LocalFieldData F).isCompact_integers

theorem isOpen_integralBox (r s : ℕ) : IsOpen (integralBox F r s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
    (⟨⟩ : LocalFieldData F).isOpen_integers

theorem zero_mem_integralBox (r s : ℕ) : (0 : Matrix (Fin r) (Fin s) F) ∈ integralBox F r s :=
  fun _ _ _ _ => ((⟨⟩ : LocalFieldData F).Integers).zero_mem

/-- The indicator of the integral box, a Schwartz–Bruhat function with value `1` at `0`. -/
def integralBoxTest (r s : ℕ) : SchwartzBruhat (Matrix (Fin r) (Fin s) F) :=
  ⟨(integralBox F r s).indicator fun _ => 1,
    ((LocallyConstant.const _ (1 : ℂ)).indicator
      ⟨(isCompact_integralBox F r s).isClosed, isOpen_integralBox F r s⟩).isLocallyConstant,
    HasCompactSupport.intro (isCompact_integralBox F r s)
      (fun _ hx => Set.indicator_of_notMem hx _)⟩

theorem integralBoxTest_apply (r s : ℕ) (X : Matrix (Fin r) (Fin s) F) :
    integralBoxTest F r s X = (integralBox F r s).indicator (fun _ => (1 : ℂ)) X := rfl

theorem integralBoxTest_zero (r s : ℕ) : integralBoxTest F r s 0 = 1 := by
  rw [integralBoxTest_apply, Set.indicator_of_mem (zero_mem_integralBox F r s)]

/-- The four blocks `((A, D), B), C` of a matrix in the block convention. -/
def blockSplit (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F) :
    ((Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F × Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F :=
  let Y := Matrix.reindex (blockEquiv h).symm (blockEquiv h).symm X
  (((Y.toBlocks₁₁, Y.toBlocks₂₂), Y.toBlocks₁₂), Y.toBlocks₂₁)

/-- The matrix with prescribed blocks `((A, D), B), C`. -/
def blockJoin (w : ((Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F ×
      Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) × Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) F :=
  Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks w.1.1.1 w.1.2 w.2 w.1.1.2)

theorem blockJoin_blockSplit (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F) :
    blockJoin F h (blockSplit F h X) = X := by
  simp only [blockJoin, blockSplit, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem blockSplit_upper (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F)
    (B : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)
    (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) :
    blockSplit F h (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D)) =
      (((A, D), B), 0) := by
  simp [blockSplit]

theorem continuous_blockSplit : Continuous (blockSplit F h) := by
  refine (((?_ : Continuous _).prodMk (?_ : Continuous _)).prodMk (?_ : Continuous _)).prodMk
    (?_ : Continuous _)
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inl i)) ((blockEquiv h) (Sum.inl j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inr i)) ((blockEquiv h) (Sum.inr j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inl i)) ((blockEquiv h) (Sum.inr j))
  · exact continuous_pi fun i => continuous_pi fun j =>
      continuous_id.matrix_elem ((blockEquiv h) (Sum.inr i)) ((blockEquiv h) (Sum.inl j))

theorem continuous_blockJoin : Continuous (blockJoin F h) := by
  unfold blockJoin
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases (blockEquiv h).symm i with a | a <;> rcases (blockEquiv h).symm j with b | b
  · exact (continuous_apply_apply a b).comp
      (continuous_fst.comp (continuous_fst.comp continuous_fst))
  · exact (continuous_apply_apply a b).comp (continuous_snd.comp continuous_fst)
  · exact (continuous_apply_apply a b).comp continuous_snd
  · exact (continuous_apply_apply a b).comp
      (continuous_snd.comp (continuous_fst.comp continuous_fst))

/-- The test `X ↦ Φ₀(A) Φ₁(D) 1_box(B) 1_box(C)` for the blocks `[[A, B], [C, D]]` of `X`. -/
def reverseTest (Φ₀ : MatrixTestFunction (m 0) F) (Φ₁ : MatrixTestFunction (m 1) F) :
    MatrixTestFunction t F :=
  SchwartzBruhat.compLeftInverse
    (SchwartzBruhat.tensor (SchwartzBruhat.tensor (SchwartzBruhat.tensor Φ₀ Φ₁)
      (integralBoxTest F (m 0 + 1) (m 1 + 1))) (integralBoxTest F (m 1 + 1) (m 0 + 1)))
    (blockSplit F h) (blockJoin F h) (continuous_blockSplit F h) (continuous_blockJoin F h)
    (blockJoin_blockSplit F h)

theorem reverseTest_upper (Φ₀ : MatrixTestFunction (m 0) F)
    (Φ₁ : MatrixTestFunction (m 1) F) (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F)
    (B : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)
    (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) :
    reverseTest F h Φ₀ Φ₁ (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D)) =
      Φ₀ A * Φ₁ D * integralBoxTest F (m 0 + 1) (m 1 + 1) B := by
  change SchwartzBruhat.tensor (SchwartzBruhat.tensor (SchwartzBruhat.tensor Φ₀ Φ₁)
      (integralBoxTest F (m 0 + 1) (m 1 + 1))) (integralBoxTest F (m 1 + 1) (m 0 + 1))
      (blockSplit F h (Matrix.reindex (blockEquiv h) (blockEquiv h) (Matrix.fromBlocks A B 0 D))) = _
  rw [blockSplit_upper]
  simp only [SchwartzBruhat.tensor_apply, integralBoxTest_zero, mul_one]

/-- The upper-block integral of the reverse test is the product of the block tests. -/
theorem upperBlockIntegral_reverseTest (Φ₀ : MatrixTestFunction (m 0) F)
    (Φ₁ : MatrixTestFunction (m 1) F)
    (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [IsFiniteMeasureOnCompacts dx]
    (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F)
    (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) :
    upperBlockIntegral h (reverseTest F h Φ₀ Φ₁) dx (A, D) =
      ((dx (integralBox F (m 0 + 1) (m 1 + 1))).toReal : ℂ) * (Φ₀ A * Φ₁ D) := by
  rw [upperBlockIntegral_apply]
  simp only [reverseTest_upper, integralBoxTest_apply]
  rw [integral_const_mul, integral_indicator_const _ (isOpen_integralBox F _ _).measurableSet,
    Complex.real_smul, mul_one, measureReal_def]
  ring

end Tests

section Subgroups

/-- A full-matrix test is invariant on both sides under some compact open subgroup
contained in any prescribed open subgroup. -/
theorem exists_compactOpen_biInvariant (Φ : MatrixTestFunction t F)
    (U : OpenSubgroup (Langlands.GeneralLinear (t + 1) F)) :
    ∃ K₀ : OpenSubgroup (Langlands.GeneralLinear (t + 1) F),
      IsCompact (K₀ : Set (Langlands.GeneralLinear (t + 1) F)) ∧ K₀ ≤ U ∧
      ∀ (l l' : K₀) (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F),
        Φ ((l : Langlands.GeneralLinear (t + 1) F).val * X *
          (l' : Langlands.GeneralLinear (t + 1) F).val) = Φ X := by
  have hW := eventually_matrixTranslate_eq Φ
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hW
  have hN : u ∩ v ∩ (U : Set (Langlands.GeneralLinear (t + 1) F)) ∈
      nhds (1 : Langlands.GeneralLinear (t + 1) F) :=
    Filter.inter_mem (Filter.inter_mem hu hv) U.mem_nhds_one
  have : NonarchimedeanGroup (Langlands.GeneralLinear (t + 1) F) :=
    (⟨⟩ : LocalFieldData F).generalLinearNonarchimedean (t + 1)
  obtain ⟨L, hLc, hLN⟩ := compactOpenSubgroupBasis _ _ hN
  refine ⟨L, hLc, fun x hx => (hLN hx).2, fun l l' X => ?_⟩
  have hmem : ((l : Langlands.GeneralLinear (t + 1) F),
      (l' : Langlands.GeneralLinear (t + 1) F)) ∈ u ×ˢ v :=
    ⟨(hLN l.property).1.1, (hLN l'.property).1.2⟩
  exact huv hmem X

/-- The modulus of the upper two-block parabolic is trivial on elements of a compact
subgroup. -/
theorem leviModulus_eq_one_of_mem (K : Subgroup (Langlands.GeneralLinear (t + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F)))
    (q : (succBlockShape m h).parabolic F)
    (hq : (q : Langlands.GeneralLinear (t + 1) F) ∈ K) :
    (⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h)
      ((succBlockShape m h).leviProjection F q) = 1 := by
  have hχ : Continuous (((⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h)).comp
      ((succBlockShape m h).leviProjection F)) :=
    ((⟨⟩ : LocalFieldData F).continuous_leviModulus (succBlockShape m h)).comp
      ((succBlockShape m h).leviProjectionContinuous F).continuous
  have hJ : IsCompact ((K.comap ((succBlockShape m h).parabolic F).subtype :
      Subgroup ((succBlockShape m h).parabolic F)) :
        Set ((succBlockShape m h).parabolic F)) :=
    ((succBlockShape m h).isClosed_parabolic F).isClosedEmbedding_subtypeVal.isCompact_preimage
      hK
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact _ hχ _ hJ hq

end Subgroups

section Realization

variable {V : Fin 2 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (V i))

set_option maxHeartbeats 1600000 in
/-- **Reverse realization.** For smooth admissible blocks, a block test and an actual
bi-smooth block coefficient in each block, there are a full-matrix test, an actual
bi-smooth coefficient of the induced representation and a nonzero constant `κ` such
that, whenever the block integrals converge at `s + m₀/2` and `s + m₁/2`, the induced
zeta integral converges at `s + t/2` and equals `κ` times the product of the two
block zeta integrals. -/
theorem exists_twoBlock_reverse_realization (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i))
    (Φ₀ : MatrixTestFunction (m 0) F) (ℓ₀ : SmoothDual (σ 0)) (v₀ : smoothVectors (σ 0))
    (Φ₁ : MatrixTestFunction (m 1) F) (ℓ₁ : SmoothDual (σ 1)) (v₁ : smoothVectors (σ 1)) :
    ∃ (Φ : MatrixTestFunction t F)
      (ℓ : SmoothDual ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ))
      (v : smoothVectors ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)) (κ : ℂ),
      κ ≠ 0 ∧ ∀ s : ℂ,
        (∀ α : MatrixTestFunction (m 0) F,
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) (biSmoothCoefficient (σ 0) ℓ₀ v₀)) →
        (∀ α : MatrixTestFunction (m 1) F,
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) (biSmoothCoefficient (σ 1) ℓ₁ v₁)) →
        Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift t)
            (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
              ℓ v) ∧
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift t)
              (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
                ℓ v) =
            κ * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ₀ (s + jpssShift (m 0))
                (biSmoothCoefficient (σ 0) ℓ₀ v₀) *
              Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ₁ (s + jpssShift (m 1))
                (biSmoothCoefficient (σ 1) ℓ₁ v₁)) := by
  classical
  obtain ⟨K, hK, hPK, hμ⟩ := exists_compactProductCoefficientFormula (V := V)
    (⟨⟩ : LocalFieldData F) (succBlockShape m h) (Nat.succ_pos t)
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μK, hHaar, hprob, hformula⟩ := hμ
  obtain ⟨E, hE⟩ := hformula σ hσa
  have : NonarchimedeanGroup (Langlands.GeneralLinear (t + 1) F) :=
    (⟨⟩ : LocalFieldData F).generalLinearNonarchimedean (t + 1)
  -- the full-matrix test and a compact open subgroup fixing it on both sides
  obtain ⟨K₁, hK₁, hK₁K, hΦinv⟩ := exists_compactOpen_biInvariant F (reverseTest F h Φ₀ Φ₁) K
  -- the pure tensor vector and functional
  let w : PiTensorProduct ℂ V := PiTensorProduct.tprod ℂ (twoFamily (X := V) v₀.val v₁.val)
  let lam : SmoothDual ((succBlockShape m h).blockTensor σ) :=
    FiniteTensor.smoothDualTensorMap σ
      (PiTensorProduct.tprod ℂ (twoFamily (X := fun i => SmoothDual (σ i)) ℓ₀ ℓ₁))
  have hm : Continuous ((succBlockShape m h).leviProjection F) :=
    ((succBlockShape m h).leviProjectionContinuous F).continuous
  have hker := (⟨⟩ : LocalFieldData F).isOpen_ker_parabolicHalfModulus (succBlockShape m h)
  obtain ⟨Hw, hHw⟩ := FiniteTensor.isSmooth_external σ hσs w
  obtain ⟨Hw', hHw'⟩ := Induction.exists_twist_comp_fixed ((succBlockShape m h).parabolic F)
    ((succBlockShape m h).leviProjection F) hm
    ((⟨⟩ : LocalFieldData F).parabolicHalfModulus (succBlockShape m h)) hker
    ((succBlockShape m h).blockTensor σ) w Hw hHw
  obtain ⟨Hl, hHl⟩ := isSmooth_smoothContragredient ((succBlockShape m h).blockTensor σ) lam
  obtain ⟨Hl', hHl'⟩ := Induction.exists_twist_comp_fixed ((succBlockShape m h).parabolic F)
    ((succBlockShape m h).leviProjection F) hm
    ((⟨⟩ : LocalFieldData F).parabolicHalfModulus (succBlockShape m h)) hker
    (smoothContragredient ((succBlockShape m h).blockTensor σ)) lam Hl hHl
  obtain ⟨K₂, hK₂, hK₂K₁, hlfix⟩ := Induction.exists_compact_conj_fixed
    ((succBlockShape m h).parabolic F) _ lam Hl' hHl' 1 K₁
  obtain ⟨K₀, hK₀, hK₀K₂, hwfix⟩ := Induction.exists_compact_conj_fixed
    ((succBlockShape m h).parabolic F) _ w Hw' hHw' 1 K₂
  have hlfix₀ : lam ∈ fixedVectors (twist ((⟨⟩ : LocalFieldData F).parabolicHalfModulus
      (succBlockShape m h)) ((smoothContragredient ((succBlockShape m h).blockTensor σ)).comp
        ((succBlockShape m h).leviProjection F)))
      (Induction.conjOpenSubgroup ((succBlockShape m h).parabolic F) K₀ 1).toSubgroup := by
    rw [fixedVectors, Representation.mem_invariants]
    intro p
    have hp : p.val ∈ Induction.conjOpenSubgroup ((succBlockShape m h).parabolic F) K₂ 1 := by
      rw [Induction.mem_conjOpenSubgroup]
      exact hK₀K₂ (Induction.mem_conjOpenSubgroup.mp p.property)
    exact (Representation.mem_invariants _ _).mp hlfix ⟨p.val, hp⟩
  -- the two compact double coset sections
  let fsec := Induction.compactDoubleCosetSection ((succBlockShape m h).parabolic F)
    (twist ((⟨⟩ : LocalFieldData F).parabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor σ).comp ((succBlockShape m h).leviProjection F)))
    K₀ hK₀ 1 w hwfix
  let hsec := Induction.compactDoubleCosetSection ((succBlockShape m h).parabolic F)
    (twist ((⟨⟩ : LocalFieldData F).parabolicHalfModulus (succBlockShape m h))
      ((smoothContragredient ((succBlockShape m h).blockTensor σ)).comp
        ((succBlockShape m h).leviProjection F)))
    K₀ hK₀ 1 lam hlfix₀
  let ℓ : SmoothDual ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) := E.symm hsec.val
  have hEℓ : E ℓ = hsec.val := E.toLinearEquiv.apply_symm_apply hsec.val
  let v : smoothVectors ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) :=
    ⟨fsec.val, (⟨⟩ : LocalFieldData F).isSmooth_normalizedProductInduced (succBlockShape m h) σ
      fsec.val⟩
  -- the kernels
  let Γ : K → Langlands.GeneralLinear (t + 1) F → ℂ := fun k y =>
    smoothDualPairing ((succBlockShape m h).blockTensor σ)
      (Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F))
      (Induction.eval _ _ fsec.val y)
  let Γ₀ : Langlands.GeneralLinear (t + 1) F → ℂ := fun y =>
    smoothDualPairing ((succBlockShape m h).blockTensor σ) lam (Induction.eval _ _ fsec.val y)
  have hΓ : Continuous fun z : K × Langlands.GeneralLinear (t + 1) F => Γ z.1 z.2 := by
    have hl := (Induction.eval_isLocallyConstant _ _ hsec.val).comp_continuous
      (continuous_subtype_val.comp (continuous_fst (X := K)
        (Y := Langlands.GeneralLinear (t + 1) F)))
    have hv := (Induction.eval_isLocallyConstant _ _ fsec.val).comp_continuous
      (continuous_snd (X := K) (Y := Langlands.GeneralLinear (t + 1) F))
    exact (hl.comp₂ hv fun a b =>
      smoothDualPairing ((succBlockShape m h).blockTensor σ) a b).continuous
  have hΓ₀c : Continuous Γ₀ :=
    ((Induction.eval_isLocallyConstant _ _ fsec.val).comp fun x =>
      smoothDualPairing ((succBlockShape m h).blockTensor σ) lam x).continuous
  have hsupp : ∀ k : K, (k : Langlands.GeneralLinear (t + 1) F) ∉
      parabolicCompactSet F h K₀ → ∀ y, Γ k y = 0 := by
    intro k hk y
    have h0 : Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F) = 0 := by
      by_contra hne
      obtain ⟨q, l, hql⟩ := Induction.compactDoubleCosetSection_mem_of_ne_zero _ _ K₀ hK₀ 1 lam
        hlfix₀ _ hne
      exact hk ⟨q, l, by rw [hql, mul_one]⟩
    simp only [Γ, h0, map_zero, LinearMap.zero_apply]
  have hΓ₀supp : ∀ y, y ∉ parabolicCompactSet F h K₀ → Γ₀ y = 0 := by
    intro y hy
    have h0 : Induction.eval _ _ fsec.val y = 0 := by
      by_contra hne
      obtain ⟨q, l, hql⟩ := Induction.compactDoubleCosetSection_mem_of_ne_zero _ _ K₀ hK₀ 1 w
        hwfix _ hne
      exact hy ⟨q, l, by rw [hql, mul_one]⟩
    simp only [Γ₀, h0, map_zero]
  -- translation in the compact variable
  have hK₀K : K₀ ≤ K := fun x hx => hK₁K (hK₂K₁ (hK₀K₂ hx))
  have htrans : ∀ (k : K) (q : (succBlockShape m h).parabolic F) (l : K₀),
      (k : Langlands.GeneralLinear (t + 1) F) =
        (q : Langlands.GeneralLinear (t + 1) F) *
          (l : Langlands.GeneralLinear (t + 1) F) →
      ∀ y, Γ k y = Γ₀ ((q : Langlands.GeneralLinear (t + 1) F)⁻¹ * y) := by
    intro k q l hkql y
    have hqK : (q : Langlands.GeneralLinear (t + 1) F) ∈ K.toSubgroup := by
      have hq : (q : Langlands.GeneralLinear (t + 1) F) =
          (k : Langlands.GeneralLinear (t + 1) F) *
            (l : Langlands.GeneralLinear (t + 1) F)⁻¹ := by
        rw [hkql, mul_inv_cancel_right]
      rw [hq]
      exact K.toSubgroup.mul_mem k.property (K.toSubgroup.inv_mem (hK₀K l.property))
    have hδ : (⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h)
        ((succBlockShape m h).leviProjection F q) = 1 :=
      leviModulus_eq_one_of_mem F h K.toSubgroup hK q hqK
    have hδ' : (⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h)
        ((succBlockShape m h).leviProjection F q⁻¹) = 1 := by
      rw [map_inv, map_inv, hδ, inv_one]
    have hhalf : (⟨⟩ : LocalFieldData F).parabolicHalfModulus (succBlockShape m h) q = 1 :=
      ((⟨⟩ : LocalFieldData F).leviHalfModulus_eq_one _ _).mpr hδ
    have hh : Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F) =
        smoothContragredient ((succBlockShape m h).blockTensor σ)
          ((succBlockShape m h).leviProjection F q) lam := by
      have happ := Induction.compactDoubleCosetSection_apply _ _ K₀ hK₀ 1 lam hlfix₀ q l
      rw [mul_one, ← hkql] at happ
      rw [happ]
      change ((((⟨⟩ : LocalFieldData F).parabolicHalfModulus (succBlockShape m h) q : ℂ) •
        ((smoothContragredient ((succBlockShape m h).blockTensor σ)).comp
          ((succBlockShape m h).leviProjection F)) q) lam) = _
      rw [hhalf, Units.val_one, one_smul]
      rfl
    have hcov := (⟨⟩ : LocalFieldData F).normalizedProductInduced_covariant
      (succBlockShape m h) σ fsec.val q⁻¹ y
    have hcov' : Induction.eval _ _ fsec.val ((q : Langlands.GeneralLinear (t + 1) F)⁻¹ * y) =
        (succBlockShape m h).blockTensor σ ((succBlockShape m h).leviProjection F q)⁻¹
          (Induction.eval _ _ fsec.val y) := by
      refine (congrArg (Induction.eval _ _ fsec.val) (congrArg (· * y) (Subgroup.coe_inv _ q).symm)).trans
        (hcov.trans ?_)
      rw [hδ', Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one, one_smul,
        map_inv]
    show smoothDualPairing ((succBlockShape m h).blockTensor σ)
        (Induction.eval _ _ hsec.val (k : Langlands.GeneralLinear (t + 1) F))
        (Induction.eval _ _ fsec.val y) =
      smoothDualPairing ((succBlockShape m h).blockTensor σ) lam
        (Induction.eval _ _ fsec.val ((q : Langlands.GeneralLinear (t + 1) F)⁻¹ * y))
    rw [hh, smoothDualPairing_smoothContragredient, hcov']
  -- the values of `Γ₀` on `P K₀`
  have hΓ₀ : ∀ (L : (succBlockShape m h).Levi F)
      (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) (l : K₀),
      Γ₀ (parabolicPoint h (L, x) * l) =
        halfModulus F h L * (biSmoothCoefficient (σ 0) ℓ₀ v₀ (L 0) *
          biSmoothCoefficient (σ 1) ℓ₁ v₁ (L 1)) := by
    intro L x l
    have hcov := (⟨⟩ : LocalFieldData F).normalizedProductInduced_covariant
      (succBlockShape m h) σ fsec.val ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ l
    have hLP : (succBlockShape m h).leviProjection F
        ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩ = L :=
      congrArg Prod.fst (parabolicCoord_parabolicPoint h (L, x))
    have hfl : Induction.eval _ _ fsec.val (l : Langlands.GeneralLinear (t + 1) F) = w := by
      have happ := Induction.compactDoubleCosetSection_apply_mul _ _ K₀ hK₀ 1 w hwfix l
      rwa [one_mul] at happ
    have hcoef := FiniteTensor.matrixCoefficient_smoothDualTensorMap_tprod σ
      (twoFamily (X := fun i => SmoothDual (σ i)) ℓ₀ ℓ₁) (twoFamily (X := V) v₀.val v₁.val) L
    rw [Fin.prod_univ_two] at hcoef
    show smoothDualPairing ((succBlockShape m h).blockTensor σ) lam
        (Induction.eval _ _ fsec.val (parabolicPoint h (L, x) * l)) = _
    rw [hcov, hLP, hfl, map_smul, smul_eq_mul]
    exact congrArg _ hcoef
  have hΦ : ∀ (l l' : K₀) (X : Matrix (Fin (t + 1)) (Fin (t + 1)) F),
      reverseTest F h Φ₀ Φ₁ ((l : Langlands.GeneralLinear (t + 1) F).val * X *
        (l' : Langlands.GeneralLinear (t + 1) F).val) = reverseTest F h Φ₀ Φ₁ X :=
    fun l l' X => hΦinv ⟨l, hK₂K₁ (hK₀K₂ l.property)⟩ ⟨l', hK₂K₁ (hK₀K₂ l'.property)⟩ X
  have hc₀ : Continuous (biSmoothCoefficient (σ 0) ℓ₀ v₀) :=
    (matrixCoefficient_isLocallyConstant (σ 0) _ _ v₀.property).continuous
  have hc₁ : Continuous (biSmoothCoefficient (σ 1) ℓ₁ v₁) :=
    (matrixCoefficient_isLocallyConstant (σ 1) _ _ v₁.property).continuous
  -- the coefficient of the induced representation
  have hcoefπ : biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
      ℓ v = fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂μK := by
    funext g
    have hform := (hE ℓ fsec.val g).2
    rw [hEℓ] at hform
    exact hform
  -- the constant
  have hHaar' := hHaar
  have hSpos : (μK {k : K | (k : Langlands.GeneralLinear (t + 1) F) ∈
      parabolicCompactSet F h K₀}).toReal ≠ 0 := by
    have hSo : IsOpen {k : K | (k : Langlands.GeneralLinear (t + 1) F) ∈
        parabolicCompactSet F h K₀} :=
      (isOpen_parabolicCompactSet F h K₀).preimage continuous_subtype_val
    have h1S : (1 : K) ∈ {k : K | (k : Langlands.GeneralLinear (t + 1) F) ∈
        parabolicCompactSet F h K₀} := ⟨1, 1, by simp⟩
    exact ENNReal.toReal_ne_zero.mpr ⟨hSo.measure_ne_zero μK ⟨1, h1S⟩, measure_ne_top μK _⟩
  have hρpos : (parabolicMeasure F h Measure.addHaar (parabolicPoint h ⁻¹'
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F)))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨parabolicMeasure_preimage_ne_zero F h _ K₀,
      parabolicMeasure_preimage_ne_top F h _ K₀.toSubgroup hK₀⟩
  have hμpos : (generalLinearHaar F t
      (K₀ : Set (Langlands.GeneralLinear (t + 1) F))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨K₀.isOpen.measure_ne_zero _ ⟨1, K₀.one_mem⟩,
      hK₀.measure_lt_top.ne⟩
  have hbox : ((Measure.addHaar : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      (integralBox F (m 0 + 1) (m 1 + 1))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(isOpen_integralBox F _ _).measure_ne_zero _
      ⟨0, zero_mem_integralBox F _ _⟩, (isCompact_integralBox F _ _).measure_lt_top.ne⟩
  refine ⟨reverseTest F h Φ₀ Φ₁, ℓ, v,
    (((μK {k : K | (k : Langlands.GeneralLinear (t + 1) F) ∈
        parabolicCompactSet F h K₀}).toReal *
      ((parabolicMeasure F h Measure.addHaar (parabolicPoint h ⁻¹'
        (K₀ : Set (Langlands.GeneralLinear (t + 1) F)))).toReal)⁻¹ *
      (generalLinearHaar F t
        (K₀ : Set (Langlands.GeneralLinear (t + 1) F))).toReal : ℝ) : ℂ) *
      (((Measure.addHaar : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
        (integralBox F (m 0 + 1) (m 1 + 1))).toReal : ℂ), ?_, ?_⟩
  · refine mul_ne_zero (Complex.ofReal_ne_zero.mpr ?_) (Complex.ofReal_ne_zero.mpr hbox)
    exact mul_ne_zero (mul_ne_zero hSpos (inv_ne_zero hρpos)) hμpos
  · intro s h₀ h₁
    obtain ⟨hconv, hval⟩ := reverse_zeta_of_kernel F h K K₀ hK₀ μK Γ hΓ Γ₀ hΓ₀c hsupp htrans
      hΓ₀supp _ _ hc₀ hc₁ hΓ₀ (reverseTest F h Φ₀ Φ₁) hΦ s h₀ h₁
    rw [hcoefπ]
    refine ⟨hconv, ?_⟩
    rw [hval]
    have hfun : (fun L : (succBlockShape m h).Levi F =>
        upperBlockIntegral h (reverseTest F h Φ₀ Φ₁) Measure.addHaar ((L 0).val, (L 1).val) *
          (leviCoefficientWeight F h (biSmoothCoefficient (σ 0) ℓ₀ v₀)
            (biSmoothCoefficient (σ 1) ℓ₁ v₁) s L * radicalWeight F h L)) =
        fun L => (((Measure.addHaar : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
          (integralBox F (m 0 + 1) (m 1 + 1))).toReal : ℂ) *
          (Φ₀ (L 0).val * Φ₁ (L 1).val *
            (leviCoefficientWeight F h (biSmoothCoefficient (σ 0) ℓ₀ v₀)
              (biSmoothCoefficient (σ 1) ℓ₁ v₁) s L * radicalWeight F h L)) := by
      funext L
      rw [upperBlockIntegral_reverseTest]
      ring
    have hZ := integral_leviCoefficientWeight F h (biSmoothCoefficient (σ 0) ℓ₀ v₀)
      (biSmoothCoefficient (σ 1) ℓ₁ v₁) s (R := 1) (fun _ => Φ₀) (fun _ => Φ₁) h₀ h₁
      (fun L => Φ₀ (L 0).val * Φ₁ (L 1).val) (fun L => by simp)
    rw [hfun, integral_const_mul, hZ, Fin.sum_univ_one]
    ring

/-- **Reverse generator input.** If both blocks satisfy the matrix analytic
assertions, then the product of actual rational values of individual block zeta
integrals lies in the Laurent span of the induced representation's values. This is
the third component of `TwoBlockMatrixGeneratorInputs`. -/
theorem twoBlock_reverse_generatorInput (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i)) (P : Fin 2 → Polynomial ℂ)
    (hblock : ∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F (σ i) (P i)) :
    ∀ (Φ₀ : MatrixTestFunction (m 0) F) (ℓ₀ : SmoothDual (σ 0))
      (v₀ : smoothVectors (σ 0)) (Φ₁ : MatrixTestFunction (m 1) F)
      (ℓ₁ : SmoothDual (σ 1)) (v₁ : smoothVectors (σ 1)) (R S : RationalFunctions),
      HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F (m 0))
        Φ₀ (biSmoothCoefficient (σ 0) ℓ₀ v₀) R →
      HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F (m 1))
        Φ₁ (biSmoothCoefficient (σ 1) ℓ₁ v₁) S →
      R * S ∈ zetaSpan (GodementJacquet.matrixRationalValues
        (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F t)
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)) := by
  intro Φ₀ ℓ₀ v₀ Φ₁ ℓ₁ v₁ R S hR hS
  obtain ⟨a₀, ha₀⟩ := (hblock 0).1
  obtain ⟨a₁, ha₁⟩ := (hblock 1).1
  obtain ⟨Φ, ℓ, v, κ, hκ, hD⟩ := exists_twoBlock_reverse_realization F h σ hσs hσa Φ₀ ℓ₀ v₀ Φ₁ ℓ₁ v₁
  have hmem₀ : biSmoothCoefficient (σ 0) ℓ₀ v₀ ∈ biSmoothMatrixCoefficients (σ 0) :=
    Submodule.subset_span ⟨ℓ₀, v₀, rfl⟩
  have hmem₁ : biSmoothCoefficient (σ 1) ℓ₁ v₁ ∈ biSmoothMatrixCoefficients (σ 1) :=
    Submodule.subset_span ⟨ℓ₁, v₁, rfl⟩
  have hconv (s : ℂ) (hs : max a₀ a₁ < s.re) :=
    hD s (fun α => ha₀ α ⟨_, hmem₀⟩ s ((le_max_left a₀ a₁).trans_lt hs))
      (fun α => ha₁ α ⟨_, hmem₁⟩ s ((le_max_right a₀ a₁).trans_lt hs))
  have hHS : HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F t) Φ
      (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) ℓ v)
      (RatFunc.C κ * (R * S)) :=
    ⟨⟨max a₀ a₁, fun s hs => (hconv s hs).1⟩,
      RationalContinuationLinear.continuation_of_eq_on_right
        (hasRationalContinuation_const_mul κ (HasRationalContinuation.mul hR.2 hS.2))
        ⟨max a₀ a₁, fun s hs => (hconv s hs).2⟩⟩
  have hπmem : RatFunc.C κ * (R * S) ∈ zetaSpan (GodementJacquet.matrixRationalValues
      (⟨⟩ : LocalFieldData F).residueCardinality
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F t)
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)) :=
    Submodule.subset_span ⟨Φ, ⟨_, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩, hHS⟩
  have hsm := Submodule.smul_mem _ (LaurentPolynomial.C κ⁻¹) hπmem
  rw [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hκ, map_one, one_mul] at hsm
  exact hsm

/-- **Two-block generator inputs.** All three components of
`TwoBlockMatrixGeneratorInputs` for the canonical normalized induced representation of
two smooth admissible blocks satisfying the matrix analytic assertions. -/
theorem twoBlock_matrixGeneratorInputs (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i)) (P : Fin 2 → Polynomial ℂ)
    (hblock : ∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F (σ i) (P i)) :
    TwoBlockMatrixGeneratorInputs (⟨⟩ : LocalFieldData F).residueCardinality
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F t)
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) m
      (fun i => generalLinearHaar F (m i)) σ :=
  ⟨(twoBlock_forward_generatorInputs F h σ hσs hσa P hblock).1,
    (twoBlock_forward_generatorInputs F h σ hσs hσa P hblock).2,
    twoBlock_reverse_generatorInput F h σ hσs hσa P hblock⟩

end Realization

end Langlands.AllField.GodementJacquet.TwoBlock
