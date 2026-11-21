import Langlands.Global.RankinSelberg.ComplexLocalDeterminantTwist
import Langlands.Global.RankinSelberg.ComplexLocalEqualJacquetExpansion
import Langlands.Global.RankinSelberg.ComplexRankZeroLocal
import Langlands.Representation.GodementJacquet.ComplexPrincipalSeriesCompactEquation
import Langlands.Global.RankinSelberg.ComplexCompactMatrixGrowth
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth

/-! # The normalized matrix factor in the complex Jacquet comparisons -/

noncomputable section

open Filter MeasureTheory Topology
open Langlands.Archimedean Langlands.GeneralLinear Langlands.GodementJacquet
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "ι" => inverseTranspose n ℂ

private theorem pairBlocks_singleton_left {m : ℕ} (d : ComplexCharacterData)
    (e : Fin m → ComplexCharacterData) :
    complexPairBlocks [d] (List.ofFn e) = List.ofFn (fun i => d.mul (e i)) := by
  simp [complexPairBlocks, List.map_ofFn, Function.comp_def]

private theorem pairGamma {m : ℕ} (d : ComplexCharacterData)
    (e : Fin m → ComplexCharacterData) (s : ℂ) :
    ((complexPairLFactor [d] (List.ofFn e)).denominator s)⁻¹ =
      complexDiagonalGamma (fun i => (d.mul (e i)).weight)
        (fun i => s + (d.mul (e i)).exponent) := by
  rw [complexPairLFactor, pairBlocks_singleton_left, denominator_complexLFactor, List.map_ofFn,
    List.prod_ofFn]
  simp only [Function.comp_apply, ComplexCharacterData.lFactor, complexTateL,
    ReciprocalEntire.denominator_shift, gammaComplex, Finset.prod_inv_distrib, inv_inv,
    complexDiagonalGamma, add_assoc]

private theorem pairGamma_dual {m : ℕ} (d : ComplexCharacterData)
    (e : Fin m → ComplexCharacterData) (s : ℂ) :
    ((complexPairLFactor ([d].map ComplexCharacterData.inv)
      ((List.ofFn e).map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ =
      complexDiagonalGamma (fun i => -(d.mul (e i)).weight)
        (fun i => 1 - (s + (d.mul (e i)).exponent)) := by
  simp only [List.map_cons, List.map_nil, List.map_ofFn, pairGamma, Function.comp_apply,
    complexDiagonalGamma, ComplexRankZero.inv_mul_exponent,
    ComplexRankZero.inv_mul_weight_natAbs, Int.natAbs_neg]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

private theorem pairEpsilon_one {m : ℕ} (d : ComplexCharacterData)
    (e : Fin m → ComplexCharacterData) (s : ℂ) :
    (complexPairEpsilon [d] (List.ofFn e) 1 ‖((1 : ℂˣ) : ℂ)‖₊
      (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ) =
      complexDiagonalStandardEpsilon (fun i => (d.mul (e i)).weight) := by
  rw [complexPairEpsilon, pairBlocks_singleton_left, coe_complexEpsilon]
  simp [complexDiagonalStandardEpsilon, List.map_ofFn, List.prod_ofFn]

private def reflectedPairDenominator (L : ReciprocalEntire) : ReciprocalEntire where
  denominator := fun s => L.denominator (1 - s)
  entire := L.entire.comp ((differentiable_const _).sub differentiable_id)
  nonzero := by
    obtain ⟨z, hz⟩ := L.nonzero
    exact ⟨1 - z, by simpa using hz⟩

private theorem pairEquation_matrix {m : ℕ} (d : ComplexCharacterData)
    (e : Fin m → ComplexCharacterData)
    (Z Zd : ℂ → ℂ) (c : ℂ)
    (hFE : ∀ s₀ : ℂ,
      (fun s : ℂ => Zd (1 - s) / complexDiagonalGamma (fun i => -(d.mul (e i)).weight)
          (fun i => 1 - (s + (d.mul (e i)).exponent))) =ᶠ[𝓝[≠] s₀]
        (fun s => complexDiagonalStandardEpsilon (fun i => (d.mul (e i)).weight) *
          (Z s / complexDiagonalGamma (fun i => (d.mul (e i)).weight)
            (fun i => s + (d.mul (e i)).exponent)))) :
    PairMeromorphicEquation [d] (List.ofFn e) 1 1 (fun s => c * Z s) (fun s => c * Zd s) := by
  unfold PairMeromorphicEquation
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro s₀
  let L := complexPairLFactor [d] (List.ofFn e)
  let Ld := complexPairLFactor ([d].map ComplexCharacterData.inv)
    ((List.ofFn e).map ComplexCharacterData.inv)
  filter_upwards [hFE s₀, L.denominator_eventually_ne_zero s₀,
    (reflectedPairDenominator Ld).denominator_eventually_ne_zero s₀] with s hs hP hD
  change Ld.denominator (1 - s) ≠ 0 at hD
  change Zd (1 - s) / complexDiagonalGamma (fun i => -(d.mul (e i)).weight)
      (fun i => 1 - (s + (d.mul (e i)).exponent)) =
    complexDiagonalStandardEpsilon (fun i => (d.mul (e i)).weight) *
      (Z s / complexDiagonalGamma (fun i => (d.mul (e i)).weight)
        (fun i => s + (d.mul (e i)).exponent)) at hs
  rw [← pairGamma d e s, ← pairGamma_dual d e s] at hs
  change Zd (1 - s) / (Ld.denominator (1 - s))⁻¹ =
    complexDiagonalStandardEpsilon (fun i => (d.mul (e i)).weight) *
      (Z s / (L.denominator s)⁻¹) at hs
  rw [div_eq_iff (inv_ne_zero hD), ← mul_div_assoc, div_mul_eq_mul_div,
    eq_div_iff (inv_ne_zero hP)] at hs
  rw [pairEpsilon_one, one_mul]
  change (L.denominator s)⁻¹ * (c * Zd (1 - s)) =
    complexDiagonalStandardEpsilon (fun i => (d.mul (e i)).weight) *
      (Ld.denominator (1 - s))⁻¹ * (c * Z s)
  linear_combination c * hs

private theorem continuous_twistedCompactWeight (d : ComplexCharacterData) (κ : Kc → ℂ)
    (hκ : Continuous κ) :
    Continuous (fun k : Kc => κ k * (d.character ((determinant k.val)⁻¹) : ℂ)) := by
  have hdet : Continuous ((determinant : G →* ℂˣ) : G → ℂˣ) := by
    apply Units.continuous_iff.mpr
    refine ⟨Units.continuous_val.matrix_det, ?_⟩
    change Continuous (fun g : G => (g⁻¹).val.det)
    exact (Units.continuous_val.comp (continuous_inv : Continuous (fun g : G => g⁻¹))).matrix_det
  exact hκ.mul (Units.continuous_val.comp
    (d.character.continuous.comp (continuous_inv.comp (hdet.comp continuous_subtype_val))))

private theorem compactCoefficient_detTwist (d : ComplexCharacterData) (ν : Measure Kc)
    (κ : Kc → ℂ) (f : G → ℂ) (g : G) :
    complexCompactCoefficient ν
        (fun k => κ k * (d.character ((determinant k.val)⁻¹) : ℂ))
        (complexDeterminantTwist d f) g =
      (d.character (determinant g) : ℂ) * complexCompactCoefficient ν κ f g := by
  rw [complexCompactCoefficient, complexCompactCoefficient, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun k => ?_
  have h : (d.character ((determinant k.val)⁻¹) : ℂ) *
      (d.character (determinant (k.val * g)) : ℂ) = (d.character (determinant g) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, map_mul determinant, inv_mul_cancel_left]
  calc
    _ = κ k * ((d.character ((determinant k.val)⁻¹) : ℂ) *
        (d.character (determinant (k.val * g)) : ℂ)) * f (k.val * g) := by
      simp only [complexDeterminantTwist]
      ring
    _ = _ := by rw [h]; ring

/-- The square matrix integrand with the determinant twist of the removed block. -/
def complexJacquetMatrixIntegrand (d : ComplexCharacterData) (b : G → ℂ)
    (Φ : M → ℂ) (s : ℂ) (g : G) : ℂ :=
  Φ g.val * (d.character (determinant g) : ℂ) *
    ArchimedeanLocal.detPower complexNormalizedAbs g (s + (r : ℂ) / 2) * b g

variable (r) in
/-- For any group Haar normalization the two matrix integrals in the standard-character
Jacquet comparison have meromorphic continuations with the singleton pair factors. -/
def ComplexLocalMatrixEquationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure Kc) [ν.IsHaarMeasure] [SFinite ν]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) (χ : ℕ → ℂˣ → ℂ),
    (∀ i : Fin n, ∀ z : ℂˣ, χ i.val z = ((e i).character z : ℂ)) →
    ∀ f : G → ℂ, f ∈ principalSeries ℂ n χ →
    ∀ κ : Kc → ℂ, Continuous κ →
    ∀ Φ : SchwartzMap M ℂ,
      let b := complexCompactCoefficient ν κ f
      ∃ (Z Zd : ℂ → ℂ), Meromorphic Z ∧ Meromorphic Zd ∧
        PairMeromorphicEquation [d] (List.ofFn e) 1 1 Z Zd ∧
        ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
          Integrable (complexJacquetMatrixIntegrand d b Φ s) μ ∧
          Integrable (complexJacquetMatrixIntegrand d.inv (b ∘ ι) (complexMatrixFourier 1 Φ) s) μ ∧
          Z s = (∫ g, complexJacquetMatrixIntegrand d b Φ s g ∂μ) ∧
          Zd s = (∫ g, complexJacquetMatrixIntegrand d.inv (b ∘ ι)
            (complexMatrixFourier 1 Φ) s g ∂μ)

theorem complexLocalMatrixEquation : ComplexLocalMatrixEquationStatement r := by
  intro μ _ ν _ _ d e χ hχ f hf κ hκ Φ
  let κ' (k : Kc) := κ k * (d.character ((determinant k.val)⁻¹) : ℂ)
  let f' := complexDeterminantTwist d f
  let e' (i : Fin n) := d.mul (e i)
  let χ' (i : ℕ) (z : ℂˣ) := (d.character z : ℂ) * χ i z
  let b := complexCompactCoefficient ν κ f
  let b' := complexCompactCoefficient ν κ' f'
  have hχ' (i : Fin n) (z : ℂˣ) : χ' i.val z = ((e' i).character z : ℂ) := by
    simp only [χ', e', ComplexCharacterData.mul, ContinuousMonoidHom.mul_apply, Units.val_mul, hχ]
  obtain ⟨Z, Zd, hZ, hZd, ⟨σ, hσ⟩, hFE⟩ :=
    complexPrincipalSeriesCompactEquation r ν e' χ' hχ' f'
      (complexLocalDeterminantTwist d χ f hf) κ' (continuous_twistedCompactWeight d κ hκ) Φ
  let μ₀ := complexMatrixHaar n (complexMatrixAddMeasure n 1)
  let : μ₀.IsHaarMeasure := complexMatrixHaar_isHaar n _
  let : LocallyCompactSpace G :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
  let : SecondCountableTopology G := Units.isInducing_embedProduct.secondCountableTopology
  let c := Measure.haarScalarFactor μ μ₀
  have hμ : μ = c • μ₀ := Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨fun s => (c : ℂ) * Z s, fun s => (c : ℂ) * Zd s, ?_, ?_,
    pairEquation_matrix d e Z Zd c hFE, σ, fun s hs => ?_⟩
  · exact fun s => (MeromorphicAt.const _ s).mul (hZ s)
  · exact fun s => (MeromorphicAt.const _ s).mul (hZd s)
  obtain ⟨hI, hId, hM, hMd⟩ := hσ s hs
  have hb' (g : G) : b' g = (d.character (determinant g) : ℂ) * b g :=
    compactCoefficient_detTwist d ν κ f g
  have hp : complexMatrixZetaIntegrand b' Φ s = complexJacquetMatrixIntegrand d b Φ s := by
    funext g
    rw [complexMatrixZetaIntegrand, hb', complexJacquetMatrixIntegrand]
    ring
  have hd : complexMatrixZetaIntegrand (b' ∘ ι) (complexMatrixFourier 1 Φ) s =
      complexJacquetMatrixIntegrand d.inv (b ∘ ι) (complexMatrixFourier 1 Φ) s := by
    funext g
    simp only [complexMatrixZetaIntegrand, Function.comp_apply, hb', complexJacquetMatrixIntegrand]
    rw [RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose, map_inv,
      Units.val_inv_eq_inv_val, ComplexCharacterData.inv_character_apply]
    ring
  rw [hp] at hI hM
  rw [hd] at hId hMd
  rw [hμ]
  refine ⟨hI.smul_measure_nnreal, hId.smul_measure_nnreal, ?_, ?_⟩
  · rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    exact congrArg ((c : ℂ) * ·) hM
  · rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    exact congrArg ((c : ℂ) * ·) hMd

private theorem matrixLFactor_inverse_denominator (d : ComplexCharacterData)
    (e : Fin n → ComplexCharacterData) (s : ℂ) :
    (complexLFactor ((List.ofFn (fun j => d.mul (e j))).map ComplexCharacterData.inv)).denominator s =
      (complexPairLFactor ([d].map ComplexCharacterData.inv)
        ((List.ofFn e).map ComplexCharacterData.inv)).denominator s := by
  simp only [complexPairLFactor, List.map_cons, List.map_nil, List.map_ofFn, pairBlocks_singleton_left,
    ComplexSquareZeta.denominator_complexLFactor_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Function.comp_apply, ComplexTateProduct.gammaNormalizer,
    ComplexCharacterData.inv_weight, ComplexCharacterData.inv_exponent, ComplexRankZero.inv_mul_exponent,
    ComplexRankZero.inv_mul_weight_natAbs, Int.natAbs_neg]

/-- The exact two twisted compact matrix integrals for any supplied group Haar
measure have entire normalizations with exponential strip growth. -/
def ComplexLocalMatrixGrowthStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure Kc) [ν.IsHaarMeasure] [SFinite ν]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) (χ : ℕ → ℂˣ → ℂ),
    (∀ i : Fin n, ∀ z : ℂˣ, χ i.val z = ((e i).character z : ℂ)) →
    ∀ f : G → ℂ, f ∈ principalSeries ℂ n χ →
    ∀ κ : Kc → ℂ, Continuous κ →
    ∀ Φ : SchwartzMap M ℂ,
      let b := complexCompactCoefficient ν κ f
      HasComplexPairNormalizedGrowth [d] (List.ofFn e) 1 1
        (fun s => ∫ g, complexJacquetMatrixIntegrand d b Φ s g ∂μ)
        (fun s => ∫ g, complexJacquetMatrixIntegrand d.inv (b ∘ ι)
          (complexMatrixFourier 1 Φ) s g ∂μ)

set_option maxHeartbeats 1150000 in
theorem complexLocalMatrixGrowth : ComplexLocalMatrixGrowthStatement (r := r) := by
  intro μ _ ν _ _ d e χ hχ f hf κ hκ Φ
  let κ' (k : Kc) := κ k * (d.character ((determinant k.val)⁻¹) : ℂ)
  let f' := complexDeterminantTwist d f
  let e' (i : Fin n) := d.mul (e i)
  let χ' (i : ℕ) (z : ℂˣ) := (d.character z : ℂ) * χ i z
  let b := complexCompactCoefficient ν κ f
  let b' := complexCompactCoefficient ν κ' f'
  have hχ' (i : Fin n) (z : ℂˣ) : χ' i.val z = ((e' i).character z : ℂ) := by
    simp only [χ', e', ComplexCharacterData.mul, ContinuousMonoidHom.mul_apply, Units.val_mul, hχ]
  obtain ⟨N, Nd, hN, hNd, hNg, hNdg, σ, hσ⟩ :=
    complexCompactMatrixGrowth ν e' χ' hχ' f' κ' Φ
      (complexLocalDeterminantTwist d χ f hf) (continuous_twistedCompactWeight d κ hκ)
  obtain ⟨Z, Zd, hZ, hZd, hFE, τ, hτ⟩ := complexLocalMatrixEquation (r := r) μ ν d e χ hχ f hf κ hκ Φ
  let μ₀ := complexMatrixHaar n (complexMatrixAddMeasure n 1)
  let : μ₀.IsHaarMeasure := complexMatrixHaar_isHaar n _
  let : LocallyCompactSpace G :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
  let : SecondCountableTopology G := Units.isInducing_embedProduct.secondCountableTopology
  let c := Measure.haarScalarFactor μ μ₀
  have hμ : μ = c • μ₀ := Measure.isMulLeftInvariant_eq_smul _ _
  let I (s : ℂ) := ∫ g, complexJacquetMatrixIntegrand d b Φ s g ∂μ
  let Id (s : ℂ) := ∫ g, complexJacquetMatrixIntegrand d.inv (b ∘ ι) (complexMatrixFourier 1 Φ) s g ∂μ
  have hb' (g : G) : b' g = (d.character (determinant g) : ℂ) * b g :=
    compactCoefficient_detTwist d ν κ f g
  have hp (s : ℂ) :
      complexMatrixZetaIntegrand b' Φ s = complexJacquetMatrixIntegrand d b Φ s := by
    funext g
    rw [complexMatrixZetaIntegrand, hb', complexJacquetMatrixIntegrand]
    ring
  have hd (s : ℂ) : complexMatrixZetaIntegrand (b' ∘ ι) (complexMatrixFourier 1 Φ) s =
      complexJacquetMatrixIntegrand d.inv (b ∘ ι) (complexMatrixFourier 1 Φ) s := by
    funext g
    simp only [complexMatrixZetaIntegrand, Function.comp_apply, hb', complexJacquetMatrixIntegrand]
    rw [RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose, map_inv,
      Units.val_inv_eq_inv_val, ComplexCharacterData.inv_character_apply]
    ring
  have hP : complexLFactor (List.ofFn e') = complexPairLFactor [d] (List.ofFn e) := by
    rw [complexPairLFactor, pairBlocks_singleton_left]
  have hright (s : ℂ) (hs : σ < s.re) :
      (c : ℂ) * N s = (complexPairLFactor [d] (List.ofFn e)).denominator s * I s ∧
      (c : ℂ) * Nd s = (complexPairLFactor ([d].map ComplexCharacterData.inv)
        ((List.ofFn e).map ComplexCharacterData.inv)).denominator s * Id s := by
    obtain ⟨hL, hLd⟩ := hσ s hs
    change N s = _ * (∫ g, complexMatrixZetaIntegrand b' Φ s g ∂μ₀) at hL
    change Nd s = _ * (∫ g, complexMatrixZetaIntegrand (b' ∘ ι) (complexMatrixFourier 1 Φ) s g ∂μ₀) at hLd
    rw [hp, hP] at hL
    rw [hd, matrixLFactor_inverse_denominator d e s] at hLd
    dsimp only [I, Id]
    rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      NNReal.smul_def, NNReal.smul_def, Complex.real_smul, Complex.real_smul, hL, hLd]
    constructor <;> ring
  have hg : HasStripExponentialGrowth (fun _ : ℂ => (c : ℂ)) :=
    fun _ _ => ⟨‖(c : ℂ)‖, 0, 0, norm_nonneg _, le_rfl, fun s _ _ _ => by simp⟩
  have he : Continuous (fun s : ℂ =>
      (complexPairEpsilon [d] (List.ofFn e) 1 ‖((1 : ℂˣ) : ℂ)‖₊
        (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ)) := by
    simp only [complexPairEpsilon_one]
    exact continuous_const
  refine ⟨fun s => (c : ℂ) * N s, fun s => (c : ℂ) * Nd s,
    hN.const_mul _, hNd.const_mul _, hg.mul hNg, hg.mul hNdg, ⟨σ, hright⟩, ?_⟩
  apply normalizedEquation_of_pairMeromorphicEquation hZ hZd hFE
    (hN.const_mul (c : ℂ)) (hNd.const_mul (c : ℂ)) he (σ := max σ τ)
  intro s hs
  obtain ⟨h₁, h₂⟩ := hright s ((le_max_left _ _).trans_lt hs)
  obtain ⟨_, _, h₃, h₄⟩ := hτ s ((le_max_right _ _).trans_lt hs)
  exact ⟨h₁.trans (congrArg (_ * ·) h₃.symm), h₂.trans (congrArg (_ * ·) h₄.symm)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
