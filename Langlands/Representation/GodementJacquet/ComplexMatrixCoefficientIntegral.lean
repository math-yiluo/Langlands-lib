import Langlands.Representation.GodementJacquet.ComplexPrincipalSeriesGrowth
import Langlands.Representation.GodementJacquet.ComplexMatrixLeftAverage

/-! # Moving a compact pairing from the matrix coefficient to the test -/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Global.RankinSelbergGlobal (complexMatrixHeight)
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Global.RankinSelbergGlobal.ComplexPlaceAnalytic
open Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange (complexMatrixHeight_mul_le)

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n

local instance coefficientIntegralGLMeasurable (m : ℕ) : MeasurableSpace (GeneralLinear m ℂ) := borel _
local instance coefficientIntegralGLBorel (m : ℕ) : BorelSpace (GeneralLinear m ℂ) := ⟨rfl⟩
local instance coefficientIntegralGLSecondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).isInducing.secondCountableTopology
local instance coefficientIntegralUnitarySecondCountable (m : ℕ) :
    SecondCountableTopology (unitaryCompact ℂ m) := IsInducing.subtypeVal.secondCountableTopology

private theorem detPower_left_unitary (k : Kc) (g : G) (s : ℂ) :
    detPower complexNormalizedAbs (k.val * g) s = detPower complexNormalizedAbs g s := by
  have hk₀ := ComplexMaximalParabolicIntegration.normSqC_det_unitary k
  have hk : complexNormalizedAbs k.val.val.det = 1 := by
    change ((complexNormalizedAbs k.val.val.det : ℝ) : ℂ) = 1 at hk₀
    exact_mod_cast hk₀
  have he : complexNormalizedAbs ((k.val * g : G).val.det) =
      complexNormalizedAbs k.val.val.det * complexNormalizedAbs g.val.det := by
    rw [Units.val_mul, Matrix.det_mul]
    simp only [complexNormalizedAbs, norm_mul, mul_pow]
  rw [detPower, detPower, he, hk, one_mul]

private theorem continuous_height : Continuous (fun g : G => complexMatrixHeight g) := by
  have h (i j : I) : Continuous (fun g : G => g.val i j) :=
    Units.continuous_val.matrix_elem i j
  unfold complexMatrixHeight
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((h i j).norm.pow 2).add (((h i j).comp continuous_inv).norm.pow 2)

private theorem measurePreserving_fiber_leftMul {P H : Type*}
    [MeasurableSpace P] [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
    (μ : Measure P) (ν : Measure H) [SFinite ν] [ν.IsMulLeftInvariant]
    {q : P → H} (hq : Measurable q) :
    MeasurePreserving (fun p : P × H => (p.1, q p.1 * p.2)) (μ.prod ν) (μ.prod ν) := by
  let E (p : P × H) := (p.1, q p.1 * p.2)
  have he : Measurable E := measurable_fst.prodMk ((hq.comp measurable_fst).mul measurable_snd)
  refine ⟨he, ?_⟩
  ext S hS
  rw [Measure.map_apply he hS, Measure.prod_apply (he hS), Measure.prod_apply hS]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun p => by
    change ν ((q p * ·) ⁻¹' (Prod.mk p ⁻¹' S)) = ν (Prod.mk p ⁻¹' S)
    rw [← Measure.map_apply (measurable_const_mul (q p)) (measurable_prodMk_left hS),
      map_mul_left_eq_self]

/-- Moving compact left translations from an averaged coefficient to a
matrix test preserves the integral on a right half-plane. -/
theorem integral_complexCompactCoefficient_changeTest (a : ℂˣ) (μK : Measure Kc) [SFinite μK]
    (κ : Kc → ℂ) (hκ : Integrable κ μK) (hκc : Continuous κ)
    (T : Kc → Kc) (hT : Continuous T) {f : G → ℂ} (hf : Continuous f) (Φ : SchwartzMap M ℂ)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hGrowth : ∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ N) {s : ℂ}
    (hs : (n : ℝ) + N ≤ (s + (r : ℂ) / 2).re) :
    let μ := complexMatrixHaar n (complexMatrixAddMeasure n a)
    let fK (g : G) := ∫ k, κ k * f ((T k).val * g) ∂μK
    let ΦK (X : M) := ∫ k, κ k * Φ (((T k).val⁻¹).val * X) ∂μK
    Integrable (complexMatrixZetaIntegrand fK Φ s) μ ∧
      (∫ g, complexMatrixZetaIntegrand fK Φ s g ∂μ) =
        ∫ g, complexMatrixZetaIntegrand f ΦK s g ∂μ := by
  dsimp only
  let μA := complexMatrixAddMeasure n a
  let μ := complexMatrixHaar n μA
  let : μ.IsHaarMeasure := complexMatrixHaar_isHaar n μA
  let : LocallyCompactSpace G :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact n
  let w := s + (r : ℂ) / 2
  let fK (g : G) := ∫ k, κ k * f ((T k).val * g) ∂μK
  let ΦK (X : M) := ∫ k, κ k * Φ (((T k).val⁻¹).val * X) ∂μK
  let F (k : Kc) (g : G) := κ k * Φ g.val * f ((T k).val * g) * detPower complexNormalizedAbs g w
  let H (g : G) := Φ g.val * ((complexMatrixHeight g : ℝ) : ℂ) ^ N * detPower complexNormalizedAbs g w
  have hmeas : Measurable (fun g : G => ((complexMatrixHeight g : ℝ) : ℂ) ^ N) :=
    (((Complex.continuous_ofReal.comp continuous_height).pow N) :
      Continuous (fun g : G => ((complexMatrixHeight g : ℝ) : ℂ) ^ N)).measurable
  have hH : Integrable H μ :=
    integrable_complexMatrixZetaKernel μA hmeas Φ zero_le_one (fun g => by
        simp only [norm_pow, Complex.norm_of_nonneg
          (zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) g)), one_mul]
        exact le_rfl) hs
  have hTk : Continuous (fun k : Kc => (T k).val) := continuous_subtype_val.comp hT
  have hform : Continuous (fun p : Kc × G => f ((T p.1).val * p.2)) :=
    hf.comp ((hTk.comp continuous_fst).mul continuous_snd)
  have hF : Measurable (Function.uncurry F) :=
    ((((hκc.comp continuous_fst).measurable.mul
      (Φ.continuous.comp (Units.continuous_val.comp continuous_snd)).measurable).mul
        hform.measurable).mul ((measurable_complexDetPower w).comp measurable_snd))
  obtain ⟨B, hB⟩ := (isCompact_range ((continuous_height.comp continuous_subtype_val).comp hT)).bddAbove
  have hB₀ : 0 ≤ B :=
    (zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) (T 1).val)).trans
      (hB (mem_range_self (1 : Kc)))
  have hFint : Integrable (Function.uncurry F) (μK.prod μ) := by
    refine (hκ.norm.mul_prod (hH.norm.const_mul (C * B ^ N))).mono' hF.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rcases p with ⟨k, g⟩
    have hg : 0 ≤ complexMatrixHeight g :=
      zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) g)
    have hh : complexMatrixHeight ((T k).val * g) ≤ B * complexMatrixHeight g :=
      (complexMatrixHeight_mul_le (T k).val g).trans
        (mul_le_mul_of_nonneg_right (hB (mem_range_self k)) hg)
    have hb : ‖f ((T k).val * g)‖ ≤ (C * B ^ N) * complexMatrixHeight g ^ N := by
      refine (hGrowth _).trans ?_
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) _)) hh _) hC
    simp only [Function.uncurry, F, H, norm_mul, norm_pow, Complex.norm_of_nonneg hg]
    calc
      _ ≤ ‖κ k‖ * ‖Φ g.val‖ * ((C * B ^ N) * complexMatrixHeight g ^ N) *
          ‖detPower complexNormalizedAbs g w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
      _ = _ := by ring
  let q (k : Kc) := (T k).val⁻¹
  let E (p : Kc × G) := (p.1, q p.1 * p.2)
  let F' (k : Kc) (g : G) := F k (q k * g)
  have he : MeasurePreserving E (μK.prod μ) (μK.prod μ) :=
    measurePreserving_fiber_leftMul μK μ hTk.inv.measurable
  have hF'int : Integrable (Function.uncurry F') (μK.prod μ) :=
    he.integrable_comp_of_integrable hFint
  have hL (g : G) : complexMatrixZetaIntegrand fK Φ s g = ∫ k, F k g ∂μK := by
    simp only [complexMatrixZetaIntegrand, fK]
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun k => by simp only [F]; ring
  have hR (g : G) : (∫ k, F' k g ∂μK) = complexMatrixZetaIntegrand f ΦK s g := by
    simp only [complexMatrixZetaIntegrand, ΦK]
    rw [← integral_mul_const, ← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun k => by
      change F k ((T k).val⁻¹ * g) =
        κ k * Φ (((T k).val⁻¹).val * g.val) * f g * detPower complexNormalizedAbs g w
      change F k (((T k)⁻¹).val * g) = _
      simp only [F, Subgroup.coe_inv, mul_inv_cancel_left, Units.val_mul]
      exact congrArg (κ k * Φ ((q k).val * g.val) * f g * ·)
        (detPower_left_unitary ((T k)⁻¹) g w)
  change Integrable (complexMatrixZetaIntegrand fK Φ s) μ ∧
    (∫ g, complexMatrixZetaIntegrand fK Φ s g ∂μ) =
      ∫ g, complexMatrixZetaIntegrand f ΦK s g ∂μ
  constructor
  · exact hFint.swap.integral_prod_left.congr (Eventually.of_forall fun g => (hL g).symm)
  · calc
      _ = ∫ g, (∫ k, F k g ∂μK) ∂μ := by simp only [hL]
      _ = ∫ p, Function.uncurry F p ∂μK.prod μ := (integral_prod_symm _ hFint).symm
      _ = ∫ p, Function.uncurry F' p ∂μK.prod μ := by
        have hm := integral_map (μ := μK.prod μ) he.measurable.aemeasurable
          (hF.aestronglyMeasurable (μ := (μK.prod μ).map E))
        rw [he.map_eq] at hm
        exact hm
      _ = ∫ g, (∫ k, F' k g ∂μK) ∂μ := integral_prod_symm _ hF'int
      _ = _ := by simp only [hR]

end Langlands.GodementJacquet
