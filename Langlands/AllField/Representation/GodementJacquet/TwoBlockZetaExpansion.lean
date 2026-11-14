import Langlands.Representation.GodementJacquet.TwoBlockZetaExpansion
import Langlands.AllField.Representation.GodementJacquet.CompactProductCoefficients
import Langlands.AllField.Representation.GodementJacquet.TwoBlockSchwartz
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
/-!
# Finite product expansion of two-block induced matrix zeta integrals

Godement–Jacquet 1972, Theorem 3.4 (printed 38–41), for two blocks: the shifted
matrix zeta integral of an actual bi-smooth coefficient of the normalized induced
representation is a finite sum of products of block matrix zeta integrals at the
block shifts, with data independent of `s`. Consequently the induced coefficients
converge on a common right half-plane and have rational values in the product of
the block Laurent spans.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet.TwoBlock hiding blockAbs blockAbs_pos continuous_determinantWeight' continuous_leviCoefficientWeight determinantWeight_mul_of_mem exists_twoBlock_zeta_expansion exists_zeta_expansion_of_kernel glSecondCountable halfModulus halfModulus_eq instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceCarrier_2 instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_2 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_2 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyCarrier_2 instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrable_leviCoefficientWeight integrable_mul_left_radical_iff integral_leviCoefficientWeight integral_mul_left_radical integral_testFunction_parabolicPoint leviCoefficientWeight leviCoefficientWeight_mul levi_weight_identity map_mul_left_radical matrixLocallyCompact matrixSecondCountable measurableEmbedding_mul_left_radical measurable_parabolicPoint measurePreserving_parabolicShift normalizedAbs_det_eq_one_of_mem parabolicMeasure parabolicMeasure_isFiniteMeasureOnCompacts parabolicMeasure_isOpenPosMeasure parabolicMeasure_preimage_ne_top parabolicMeasure_preimage_ne_zero parabolicMeasure_sigmaFinite parabolicPoint_translation radicalWeight twoBlock_forward_generatorInputs
open Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet hiding compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant
open Langlands.AllField.GodementJacquet

open Langlands.GeneralLinear
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Weights

end Weights

section Padic

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

/-- The complex half modulus `δ_P(L)^(1/2)` of the two-block Levi, as in the covariance
law `normalizedProductInduced_covariant`. -/
def halfModulus (L : (succBlockShape m h).Levi F) : ℂ :=
  ((NNReal.sqrt ((⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h) L : ℝ≥0) : ℝ) : ℂ)

/-- The real block determinant norm `|det (L i)|`. -/
def blockAbs (L : (succBlockShape m h).Levi F) (i : Fin 2) : ℝ :=
  (((⟨⟩ : LocalFieldData F).determinantNorm (m i + 1) (L i) : ℝ≥0) : ℝ)

theorem blockAbs_pos (L : (succBlockShape m h).Levi F) (i : Fin 2) :
    0 < blockAbs F h L i :=
  NNReal.coe_pos.mpr (Units.zero_lt _)

/-- For two blocks, `δ_P(a, d) = |det a|^(n₁) / |det d|^(n₀)`. -/
theorem halfModulus_eq (L : (succBlockShape m h).Levi F) :
    halfModulus F h L =
      ((Real.sqrt (blockAbs F h L 0 ^ (m 1 + 1) / blockAbs F h L 1 ^ (m 0 + 1)) : ℝ) : ℂ) := by
  rw [halfModulus, Real.coe_sqrt, Langlands.LocalFieldData.leviModulus_apply]
  congr 3
  rw [Fin.prod_univ_two, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_two,
    Fin.prod_univ_two]
  simp only [lt_self_iff_false, ite_false, Fin.not_lt_zero, mul_one, one_mul]
  simp only [show (0 : Fin 2) < 1 from by decide, ↓reduceIte]
  rw [Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_pow]
  rfl

/-- Elements of a compact subgroup have determinant of absolute value one. -/
theorem normalizedAbs_det_eq_one_of_mem {n : ℕ} (K : Subgroup (Langlands.GeneralLinear n F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear n F))) {k : Langlands.GeneralLinear n F}
    (hk : k ∈ K) : normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) k.val.det = 1 := by
  have h1 := (⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_mem_compact n K hK k hk
  have h2 := congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) h1
  simpa using h2

/-- The determinant weight is unchanged by two-sided translation by a compact subgroup. -/
theorem determinantWeight_mul_of_mem {n : ℕ} (K : Subgroup (Langlands.GeneralLinear n F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear n F)))
    {k k' : Langlands.GeneralLinear n F} (hk : k ∈ K) (hk' : k' ∈ K)
    (y : Langlands.GeneralLinear n F) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (k⁻¹ * y * k') s =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) y s := by
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul,
    normalizedAbs_det_eq_one_of_mem F K hK hk', normalizedAbs_det_eq_one_of_mem F K hK
      (K.inv_mem hk), one_mul, mul_one]

/-- **Levi weight identity.** In parabolic coordinates, the shifted determinant
weight times `δ_P^(1/2)` and the radical factor is the product of the shifted block
weights: `s + t/2` on `GL_(t+1)` becomes `s + m₀/2` and `s + m₁/2` on the blocks. -/
theorem levi_weight_identity (L : (succBlockShape m h).Levi F)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (parabolicPoint h (L, x)) (s + jpssShift t) * halfModulus F h L *
        radicalWeight F h L =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (L 0)
          (s + jpssShift (m 0)) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (L 1)
          (s + jpssShift (m 1)) := by
  have hA := blockAbs_pos F h L 0
  have hD := blockAbs_pos F h L 1
  have hw := weight_identity (TwoBlockJacquet.blockRanks_add h) hA hD s
  simp only [determinantWeight, det_parabolicPoint, map_mul, halfModulus_eq, radicalWeight,
    jpssShift]
  exact hw

section LeviIntegrals

variable (c₀ : Langlands.GeneralLinear (m 0 + 1) F → ℂ)
  (c₁ : Langlands.GeneralLinear (m 1 + 1) F → ℂ) (s : ℂ)

/-- The Levi function `|det L|^(s + t/2) δ_P(L)^(1/2) c₀(a) c₁(d)` of a pair of block
coefficients. -/
def leviCoefficientWeight (L : (succBlockShape m h).Levi F) : ℂ :=
  determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (parabolicPoint h (L, 0)) (s + jpssShift t) * halfModulus F h L * (c₀ (L 0) * c₁ (L 1))

/-- Products of block test functions against the Levi weight are products of the
block zeta integrands at `s + m₀/2` and `s + m₁/2`. -/
theorem leviCoefficientWeight_mul (α₀ : MatrixTestFunction (m 0) F)
    (α₁ : MatrixTestFunction (m 1) F) (L : (succBlockShape m h).Levi F) :
    α₀ (L 0).val * α₁ (L 1).val *
        (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L) =
      Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F α₀ (s + jpssShift (m 0)) c₀ (L 0) *
        Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F α₁ (s + jpssShift (m 1)) c₁ (L 1) := by
  have hw := levi_weight_identity F h L 0 s
  simp only [Langlands.AllField.GodementJacquet.Padic.matrixIntegrand, GodementJacquet.matrixIntegrand, leviCoefficientWeight]
  calc α₀ (L 0).val * α₁ (L 1).val *
        (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (parabolicPoint h (L, 0)) (s + jpssShift t) * halfModulus F h L *
            (c₀ (L 0) * c₁ (L 1)) * radicalWeight F h L)
      = α₀ (L 0).val * α₁ (L 1).val * (c₀ (L 0) * c₁ (L 1)) *
          (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (parabolicPoint h (L, 0)) (s + jpssShift t) * halfModulus F h L *
              radicalWeight F h L) := by ring
    _ = _ := by rw [hw]; ring

/-- Integrability hypothesis of the parabolic reduction, from block convergence. -/
theorem integrable_leviCoefficientWeight
    (h₀ : ∀ α : MatrixTestFunction (m 0) F,
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) c₀)
    (h₁ : ∀ α : MatrixTestFunction (m 1) F,
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) c₁)
    (α : SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F ×
      Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F)) :
    Integrable (fun L : (succBlockShape m h).Levi F =>
        α ((L 0).val, (L 1).val) * (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L))
      (Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)) := by
  obtain ⟨N, α₀, α₁, hα⟩ := SchwartzBruhat.exists_tensor_expansion α
  have he : (fun L : (succBlockShape m h).Levi F =>
      α ((L 0).val, (L 1).val) * (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L)) =
      fun L => ∑ q, Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F (α₀ q) (s + jpssShift (m 0)) c₀ (L 0) *
        Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F (α₁ q) (s + jpssShift (m 1)) c₁ (L 1) := by
    funext L
    rw [hα, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => leviCoefficientWeight_mul F h c₀ c₁ s (α₀ q) (α₁ q) L
  rw [he]
  exact integrable_finsetSum _ fun q _ =>
    integrable_pi_two_mul (fun i : Fin 2 => generalLinearHaar F (m i)) (h₀ (α₀ q))
      (h₁ (α₁ q))

/-- The Levi integral of a product test function against the weight is a product of
block zeta integrals. -/
theorem integral_leviCoefficientWeight {R : ℕ}
    (Ψ₀ : Fin R → MatrixTestFunction (m 0) F)
    (Ψ₁ : Fin R → MatrixTestFunction (m 1) F)
    (h₀ : ∀ α : MatrixTestFunction (m 0) F,
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) c₀)
    (h₁ : ∀ α : MatrixTestFunction (m 1) F,
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) c₁)
    (Θ : (succBlockShape m h).Levi F → ℂ)
    (hΘ : ∀ L, Θ L = ∑ r, Ψ₀ r (L 0).val * Ψ₁ r (L 1).val) :
    ∫ L, Θ L * (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L)
        ∂(Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)) =
      ∑ r, Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ r) (s + jpssShift (m 0)) c₀ *
        Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ r) (s + jpssShift (m 1)) c₁ := by
  have he : (fun L : (succBlockShape m h).Levi F =>
      Θ L * (leviCoefficientWeight F h c₀ c₁ s L * radicalWeight F h L)) =
      fun L => ∑ r, Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F (Ψ₀ r) (s + jpssShift (m 0)) c₀ (L 0) *
        Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F (Ψ₁ r) (s + jpssShift (m 1)) c₁ (L 1) := by
    funext L
    rw [hΘ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => leviCoefficientWeight_mul F h c₀ c₁ s (Ψ₀ r) (Ψ₁ r) L
  have hint : ∀ r ∈ (Finset.univ : Finset (Fin R)), Integrable
      (fun L : (succBlockShape m h).Levi F =>
        Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F (Ψ₀ r) (s + jpssShift (m 0)) c₀ (L 0) *
          Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F (Ψ₁ r) (s + jpssShift (m 1)) c₁ (L 1))
      (Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)) := fun r _ =>
    integrable_pi_two_mul (fun i : Fin 2 => generalLinearHaar F (m i)) (h₀ (Ψ₀ r))
      (h₁ (Ψ₁ r))
  rw [he, integral_finsetSum _ hint]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_pi_two_mul (fun i : Fin 2 => generalLinearHaar F (m i)) _ _

theorem continuous_leviCoefficientWeight (hc₀ : Continuous c₀) (hc₁ : Continuous c₁) :
    Continuous (leviCoefficientWeight F h c₀ c₁ s) := by
  unfold leviCoefficientWeight halfModulus
  have hdw : Continuous fun g : Langlands.GeneralLinear (t + 1) F =>
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (s + jpssShift t) := by
    unfold determinantWeight
    have hc : Continuous fun g : Langlands.GeneralLinear (t + 1) F =>
        ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det g.val) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp
        ((⟨⟩ : LocalFieldData F).determinantNormContinuous (t + 1)).continuous))
    refine hc.cpow continuous_const fun g => ?_
    rw [Complex.ofReal_mem_slitPlane]
    exact (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos g.det_ne_zero
  have hP : Continuous fun L : (succBlockShape m h).Levi F => parabolicPoint h (L, 0) :=
    (continuous_parabolicPoint h F).comp (continuous_id.prodMk continuous_const)
  have hδ : Continuous fun L : (succBlockShape m h).Levi F =>
      ((NNReal.sqrt ((⟨⟩ : LocalFieldData F).leviModulus (succBlockShape m h) L : ℝ≥0) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (NNReal.continuous_sqrt.comp
      (Units.continuous_val.comp ((⟨⟩ : LocalFieldData F).continuous_leviModulus _))))
  exact ((hdw.comp hP).mul hδ).mul ((hc₀.comp (continuous_apply 0)).mul
    (hc₁.comp (continuous_apply 1)))

end LeviIntegrals

section Expansion

/-- Continuity of the shifted determinant weight on `GL_(n+1)`. -/
theorem continuous_determinantWeight' (n : ℕ) (s : ℂ) :
    Continuous fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s := by
  unfold determinantWeight
  have hc : Continuous fun g : Langlands.GeneralLinear (n + 1) F =>
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det g.val) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp
      ((⟨⟩ : LocalFieldData F).determinantNormContinuous (n + 1)).continuous))
  refine hc.cpow continuous_const fun g => ?_
  rw [Complex.ofReal_mem_slitPlane]
  exact (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos g.det_ne_zero

/-- **Abstract two-block zeta expansion.** Let `K` be a compact open subgroup with
`GL_(t+1) = P K`, `ν` a finite measure on `K`, and `Γ k y` a continuous kernel whose
values on `parabolicPoint (L, x) * k'` expand as
`δ_P(L)^(1/2) ∑ j, φ j (k, k') c₀ j (a) c₁ j (d)`. Then, for a full-matrix test `Φ`,
there are finite data independent of `s` such that whenever every block test
converges against the `c₀ j` at `s + m₀/2` and against the `c₁ j` at `s + m₁/2`, the
matrix zeta integral of the coefficient `g ↦ ∫ k, Γ k (k g) dν` converges at
`s + t/2` and equals `∑ i, w i Z₀(Ψ₀ i, c₀ (jj i)) Z₁(Ψ₁ i, c₁ (jj i))`. -/
theorem exists_zeta_expansion_of_kernel
    (K : OpenSubgroup (Langlands.GeneralLinear (t + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (t + 1) F)))
    (hPK : ∀ g : Langlands.GeneralLinear (t + 1) F,
      ∃ (q : (succBlockShape m h).parabolic F) (k : K),
        g = (q : Langlands.GeneralLinear (t + 1) F) *
          (k : Langlands.GeneralLinear (t + 1) F))
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
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
      ∀ s : ℂ,
        (∀ j (α : MatrixTestFunction (m 0) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) (c₀ j)) →
        (∀ j (α : MatrixTestFunction (m 1) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) (c₁ j)) →
        Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift t)
            (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂ν) ∧
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift t)
              (fun g => ∫ k, Γ k ((k : Langlands.GeneralLinear (t + 1) F) * g) ∂ν) =
            ∑ i, w i * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ i) (s + jpssShift (m 0)) (c₀ (jj i)) *
              Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ i) (s + jpssShift (m 1)) (c₁ (jj i))) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set μ := generalLinearHaar F t with hμ
  set dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) := Measure.addHaar
    with hdx
  set ρ := parabolicMeasure F h dx with hρ
  have hemb : MeasurableEmbedding (Subtype.val : K → Langlands.GeneralLinear (t + 1) F) :=
    K.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  set ν' : Measure K := μ.comap Subtype.val with hν'def
  have hν' : ν'.map Subtype.val = μ.restrict (K : Set (Langlands.GeneralLinear (t + 1) F)) := by
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
  set W : Fin Lc → Fin N → ℂ := fun l j => ∫ z, χ l z * φ j z ∂(ν.prod ν') with hW
  refine ⟨Σ l : Fin Lc, Fin (R l) × Fin N, inferInstance,
    fun i => ((C⁻¹ : ℝ) : ℂ) * W i.1 i.2.2, fun i => Ψ₀ i.1 i.2.1, fun i => Ψ₁ i.1 i.2.1,
    fun i => i.2.2, ?_⟩
  intro s h₀ h₁
  have hK2 : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology
      (K : Set (Langlands.GeneralLinear (t + 1) F))
  set H : Langlands.GeneralLinear (t + 1) F → ℂ := fun g =>
    Φ g.val * determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
      (s + jpssShift t) with hH
  set U : Fin N → (succBlockShape m h).Levi F → ℂ := fun j =>
    leviCoefficientWeight F h (c₀ j) (c₁ j) s with hU
  set Q : Fin Lc × Fin N → (succBlockShape m h).Levi F ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ := fun lj z =>
    Φl lj.1 (parabolicPoint h z).val * U lj.2 z.1 with hQdef
  set ψ : Fin Lc × Fin N → K → K → ℂ := fun lj k k' => χ lj.1 (k, k') * φ lj.2 (k, k')
    with hψdef
  -- measurability of the substituted kernel
  have hHc : Continuous H :=
    (Φ.continuous.comp Units.continuous_val).mul (continuous_determinantWeight' F t _)
  have hm : AEStronglyMeasurable (fun z : K × Langlands.GeneralLinear (t + 1) F =>
      H ((z.1 : Langlands.GeneralLinear (t + 1) F)⁻¹ * z.2) * Γ z.1 z.2) (ν.prod μ) :=
    ((hHc.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd)).mul
      hΓ).aestronglyMeasurable
  have hψ : ∀ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)),
      Integrable (fun z : K × K => ψ lj z.1 z.2) (ν.prod ν') := by
    intro lj _
    exact ((χ lj.1).continuous.mul (φ lj.2).continuous).integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
  have hPstep (lj : Fin Lc × Fin N) := integral_testFunction_parabolicPoint F h dx (Φl lj.1)
    (U lj.2) (continuous_leviCoefficientWeight F h (c₀ lj.2) (c₁ lj.2) s (hc₀ lj.2)
      (hc₁ lj.2)).aestronglyMeasurable
    (integrable_leviCoefficientWeight F h (c₀ lj.2) (c₁ lj.2) s (h₀ lj.2) (h₁ lj.2))
  have hQ : ∀ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)), Integrable (Q lj) ρ :=
    fun lj _ => (hPstep lj).1
  -- the expansion in factorization coordinates
  have hexp' : ∀ (k k' : K) (z : (succBlockShape m h).Levi F ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F),
      H ((k : Langlands.GeneralLinear (t + 1) F)⁻¹ *
          (parabolicPoint h z * (k' : Langlands.GeneralLinear (t + 1) F))) *
        Γ k (parabolicPoint h z * (k' : Langlands.GeneralLinear (t + 1) F)) =
      ∑ lj ∈ (Finset.univ : Finset (Fin Lc × Fin N)), ψ lj k k' * Q lj z := by
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
  obtain ⟨hint, hval⟩ := CompactFactorization.integrable_integral_coefficient_of_expansion μ
    K.toSubgroup K.isOpen.measurableSet ρ (parabolicPoint h) (measurable_parabolicPoint F h)
    (exists_parabolicPoint_mul h K.toSubgroup hPK) (parabolicPoint_translation F h dx)
    (parabolicMeasure_preimage_ne_zero F h dx K)
    (parabolicMeasure_preimage_ne_top F h dx K.toSubgroup hK)
    ν Subtype.val continuous_subtype_val.measurable ν' Subtype.val
    continuous_subtype_val.measurable hν' H Γ hm Finset.univ ψ Q hψ hQ hexp'
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
    rw [hfun, hval]
    have hQval : ∀ l j, ∫ z, Q (l, j) z ∂ρ =
        ∑ r, Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ l r) (s + jpssShift (m 0)) (c₀ j) *
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ l r) (s + jpssShift (m 1)) (c₁ j) := by
      intro l j
      rw [(hPstep (l, j)).2]
      exact integral_leviCoefficientWeight F h (c₀ j) (c₁ j) s (Ψ₀ l) (Ψ₁ l) (h₀ j) (h₁ j) _
        (fun L => hΨ l _ _)
    have hψval : ∀ l j, ∫ z, ψ (l, j) z.1 z.2 ∂(ν.prod ν') = W l j := fun l j => rfl
    rw [Fintype.sum_sigma, Fintype.sum_prod_type, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hQval l j, hψval l j, Finset.mul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hCeq : (ρ (parabolicPoint h ⁻¹'
        ((K.toSubgroup : Subgroup (Langlands.GeneralLinear (t + 1) F)) :
          Set (Langlands.GeneralLinear (t + 1) F)))).toReal = C := rfl
    rw [Complex.real_smul, hCeq]
    ring

end Expansion

section Forward

variable {V : Fin 2 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (V i))

/-- **Forward expansion.** For smooth admissible blocks, a full-matrix test `Φ` and
an actual bi-smooth coefficient of the normalized induced representation, there are
finitely many block tests and actual block bi-smooth coefficients, chosen
independently of `s`, such that whenever all block integrals converge at
`s + m₀/2` and `s + m₁/2`, the induced zeta integral converges at `s + t/2` and is the
corresponding finite sum of products of block zeta integrals. -/
theorem exists_twoBlock_zeta_expansion (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i)) (Φ : MatrixTestFunction t F)
    (ℓ : SmoothDual ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ))
    (v : smoothVectors ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℂ) (Ψ₀ : ι → MatrixTestFunction (m 0) F)
      (Ψ₁ : ι → MatrixTestFunction (m 1) F)
      (f₀ : ι → biSmoothMatrixCoefficients (σ 0)) (f₁ : ι → biSmoothMatrixCoefficients (σ 1)),
      ∀ s : ℂ,
        (∀ (c : biSmoothMatrixCoefficients (σ 0)) (α : MatrixTestFunction (m 0) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) c.val) →
        (∀ (c : biSmoothMatrixCoefficients (σ 1)) (α : MatrixTestFunction (m 1) F),
          Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) c.val) →
        Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift t)
            (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
              ℓ v) ∧
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift t)
              (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
                ℓ v) =
            ∑ i, w i * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ i) (s + jpssShift (m 0)) (f₀ i).val *
              Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ i) (s + jpssShift (m 1)) (f₁ i).val) := by
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
  obtain ⟨ι, hι, w, Ψ₀, Ψ₁, jj, hA⟩ := exists_zeta_expansion_of_kernel F h K hK hPK μK Γ hΓ φ
    c₀ c₁ hc₀ hc₁ hexp Φ
  refine ⟨ι, hι, w, Ψ₀, Ψ₁, fun i => ⟨c₀ (jj i), hmem₀ (jj i)⟩,
    fun i => ⟨c₁ (jj i), hmem₁ (jj i)⟩, ?_⟩
  intro s h₀ h₁
  rw [hcoef]
  exact hA s (fun j α => h₀ ⟨c₀ j, hmem₀ j⟩ α) (fun j α => h₁ ⟨c₁ j, hmem₁ j⟩ α)

/-- **Forward generator inputs.** If both blocks satisfy the matrix analytic
assertions, then the actual bi-smooth coefficients of the induced representation
converge on one common right half-plane, and each of their shifted zeta integrals
has a rational value in the product of the two block Laurent spans. -/
theorem twoBlock_forward_generatorInputs (hσs : ∀ i, IsSmooth (σ i))
    (hσa : ∀ i, IsAdmissible (σ i)) (P : Fin 2 → Polynomial ℂ)
    (hblock : ∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F (σ i) (P i)) :
    (∃ a : ℝ, ∀ (Φ : MatrixTestFunction t F)
      (ℓ : SmoothDual ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ))
      (v : smoothVectors ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)) (s : ℂ),
      a < s.re →
        MatrixConverges (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (generalLinearHaar F t) Φ (s + jpssShift t)
          (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
            ℓ v)) ∧
    (∀ (Φ : MatrixTestFunction t F)
      (ℓ : SmoothDual ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ))
      (v : smoothVectors ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)),
      ∃ R, HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F t) Φ
          (biSmoothCoefficient ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) ℓ v)
          R ∧
        R ∈ zetaSpan (GodementJacquet.matrixRationalValues
              (⟨⟩ : LocalFieldData F).residueCardinality
              (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              (generalLinearHaar F (m 0)) (σ 0)) *
            zetaSpan (GodementJacquet.matrixRationalValues
              (⟨⟩ : LocalFieldData F).residueCardinality
              (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              (generalLinearHaar F (m 1)) (σ 1))) := by
  classical
  obtain ⟨a₀, ha₀⟩ := (hblock 0).1
  obtain ⟨a₁, ha₁⟩ := (hblock 1).1
  have hconv (s : ℂ) (hs : max a₀ a₁ < s.re) :
      (∀ (c : biSmoothMatrixCoefficients (σ 0)) (α : MatrixTestFunction (m 0) F),
        Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 0)) c.val) ∧
      (∀ (c : biSmoothMatrixCoefficients (σ 1)) (α : MatrixTestFunction (m 1) F),
        Langlands.AllField.GodementJacquet.Padic.MatrixConverges F α (s + jpssShift (m 1)) c.val) :=
    ⟨fun c α => ha₀ α c s ((le_max_left a₀ a₁).trans_lt hs),
      fun c α => ha₁ α c s ((le_max_right a₀ a₁).trans_lt hs)⟩
  refine ⟨⟨max a₀ a₁, fun Φ ℓ v s hs => ?_⟩, fun Φ ℓ v => ?_⟩
  · obtain ⟨ι, _, w, Ψ₀, Ψ₁, f₀, f₁, hB⟩ := exists_twoBlock_zeta_expansion F h σ hσs hσa Φ ℓ v
    exact (hB s (hconv s hs).1 (hconv s hs).2).1
  · obtain ⟨ι, _, w, Ψ₀, Ψ₁, f₀, f₁, hB⟩ := exists_twoBlock_zeta_expansion F h σ hσs hσa Φ ℓ v
    have hR₀ := fun i => (hblock 0).2.1 (Ψ₀ i) (f₀ i)
    have hR₁ := fun i => (hblock 1).2.1 (Ψ₁ i) (f₁ i)
    choose R₀ hR₀ using hR₀
    choose R₁ hR₁ using hR₁
    refine ⟨∑ i, RatFunc.C (w i) * (R₀ i * R₁ i), ⟨⟨max a₀ a₁, fun s hs =>
      (hB s (hconv s hs).1 (hconv s hs).2).1⟩, ?_⟩, ?_⟩
    · refine RationalContinuationLinear.continuation_of_eq_on_right
        (RationalContinuationLinear.continuation_sum Finset.univ
        (fun i s => w i * (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₀ i) (s + jpssShift (m 0)) (f₀ i).val *
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (Ψ₁ i) (s + jpssShift (m 1)) (f₁ i).val))
        (fun i => RatFunc.C (w i) * (R₀ i * R₁ i))
        (fun i _ => hasRationalContinuation_const_mul (w i) (HasRationalContinuation.mul (hR₀ i).2 (hR₁ i).2)))
        ⟨max a₀ a₁, fun s hs => (hB s (hconv s hs).1 (hconv s hs).2).2⟩
    · refine Submodule.sum_mem _ fun i _ => ?_
      have hmem : R₀ i * R₁ i ∈ zetaSpan (GodementJacquet.matrixRationalValues
            (⟨⟩ : LocalFieldData F).residueCardinality
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (generalLinearHaar F (m 0)) (σ 0)) *
          zetaSpan (GodementJacquet.matrixRationalValues
            (⟨⟩ : LocalFieldData F).residueCardinality
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (generalLinearHaar F (m 1)) (σ 1)) :=
        Submodule.mul_mem_mul (Submodule.subset_span ⟨Ψ₀ i, f₀ i, hR₀ i⟩)
          (Submodule.subset_span ⟨Ψ₁ i, f₁ i, hR₁ i⟩)
      simpa only [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C] using
        Submodule.smul_mem _ (LaurentPolynomial.C (w i)) hmem

end Forward

end Padic

end Langlands.AllField.GodementJacquet.TwoBlock
