import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.ComplexRankZeroNormalization
import Langlands.Global.RankinSelberg.ComplexRankZeroWhittaker
import Langlands.Global.RankinSelberg.RealMatrixHeightBounds
import Langlands.Global.RankinSelberg.RealRankZeroNormalization
import Langlands.Global.RankinSelberg.RealWhittakerEvaluation
import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Representation.Archimedean.RealRankOneStandardModule

/-! # Ordinary normalized tests for `GL₁ × GL₁` -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal
open FunctionalEquationComparison.CompletedEquationAdapter

namespace RealRankZero

open RealRankOneStandardModule

private theorem norm_characterVector (c : RealCharacterData) (g : G) :
    ‖characterVector c g‖ = |g.val.det| ^ c.exponent.re := by
  have hpos : 0 < |g.val.det| := abs_pos.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have hsign : |g.val.det / (|g.val.det|)| = 1 := by
    rw [abs_div, abs_abs, div_self hpos.ne']
  rw [characterVector, c.character_eq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  change |g.val.det / (|g.val.det|)| ^ c.parity.val *
    ‖((|g.val.det| : ℝ) : ℂ) ^ c.exponent‖ = _
  rw [hsign, one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]

private theorem isRealWhittakerIntertwiner_scaled_subtype (c : RealCharacterData) (a : ℝˣ)
    (z : ℂ) : IsRealWhittakerIntertwiner 0 [.character c] a (z • (KF c).subtype) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f u hu g
    have h : u = 1 := upperUnipotent_eq_one ⟨u, hu⟩
    simp [h, realWhittakerCharacter]
  · intro f
    change ContMDiff (matrixModel ℝ 1) 𝓘(ℝ, ℂ) ∞ (z • (f : G → ℂ))
    exact ((z • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp f.2.1.1.1
  · intro f
    obtain ⟨C, N, _, hC⟩ :=
      RealPlaceRestriction.exists_det_rpow_le_realMatrixHeight (by decide : 0 < 1) c.exponent.re
    refine ⟨‖z‖ * ‖(f : G → ℂ) 1‖ * C, N, fun g => ?_⟩
    change ‖z * (f : G → ℂ) g‖ ≤ _
    rw [eval_formula c f.2.1.1, norm_mul, norm_mul, norm_characterVector]
    calc
      _ = (‖z‖ * ‖(f : G → ℂ) 1‖) * |g.val.det| ^ c.exponent.re := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hC g) (show 0 ≤ ‖z‖ * ‖(f : G → ℂ) 1‖ by positivity)
  · intro k f f' hf
    funext g
    change z * (f' : G → ℂ) g = z * (f : G → ℂ) (g * (k : G))
    exact congrArg (z * ·) (congrFun hf g)
  · intro X f f' hf
    change z • (f' : G → ℂ) = rightDerivative (matrixModel ℝ 1) X (z • (f : G → ℂ))
    rw [hf, rightDerivative_smul f.2.1.1.1]

/-- Each function of the real rank-one Whittaker model is a scalar multiple of the
specified character composed with determinant. -/
theorem exists_eq_of_mem_realWhittakerModel {c : RealCharacterData} {a : ℝˣ}
    {W : G → ℂ} (hW : W ∈ realWhittakerModel 0 [.character c] a) :
    ∃ C : ℂ, ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ) := by
  have hle : realWhittakerModel 0 [.character c] a ≤ Submodule.span ℂ {characterVector c} := by
    refine iSup₂_le fun B hB => ?_
    let f₀ : KF c := (evalEquiv c).symm 1
    let z := B f₀ 1
    have hB' : B = z • (KF c).subtype := by
      apply realWhittakerEvaluation 0 [.character c] a B _ hB
        (isRealWhittakerIntertwiner_scaled_subtype c a z)
      intro f
      have hf : f = (f : G → ℂ) 1 • f₀ := by
        apply (evalEquiv c).injective
        rw [map_smul, show evalEquiv c f₀ = 1 from (evalEquiv c).apply_symm_apply 1, smul_eq_mul,
          mul_one]
        rfl
      change B f 1 = z * (f : G → ℂ) 1
      conv_lhs => rw [hf, map_smul]
      exact mul_comm _ _
    rintro _ ⟨f, rfl⟩
    rw [hB']
    refine Submodule.mem_span_singleton.mpr ⟨z * (f : G → ℂ) 1, ?_⟩
    funext g
    change (z * (f : G → ℂ) 1) * characterVector c g = z * (f : G → ℂ) g
    rw [eval_formula c f.2.1.1 g]
    ring
  obtain ⟨C, hC⟩ := Submodule.mem_span_singleton.mp (hle hW)
  exact ⟨C, fun g => congrFun hC.symm g⟩

end RealRankZero

private theorem normalization_of_denominator {I R : ℂ → ℂ} (L : ReciprocalEntire)
    (hR : AnalyticOnNhd ℂ R univ)
    (hL : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0)
    (hEq : ∃ b : ℝ, ∀ s : ℂ, b < s.re → R s = I s * L.denominator s) :
    Nonempty (OrdinaryIntegralNormalization I (fun s => (L.denominator s)⁻¹)) := by
  obtain ⟨b, hb⟩ := hL
  obtain ⟨c, hc⟩ := hEq
  refine ⟨⟨R, hR, max b c, fun s hs => ?_⟩⟩
  rw [hc s ((le_max_right b c).trans_lt hs), mul_assoc,
    mul_inv_cancel₀ (hb s ((le_max_left b c).trans_lt hs)), mul_one]

private theorem finiteNormalizationSum_of_exact {Test : Type*} (I : Test → ℂ → ℂ)
    (L : ReciprocalEntire) (i : Test)
    (h : ∃ b : ℝ, ∀ s : ℂ, b < s.re → I i s = (L.denominator s)⁻¹) :
    HasFiniteOrdinaryNormalizationSum I L := by
  let N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹) :=
    ⟨fun _ => 1, fun _ _ => analyticAt_const, by simpa only [one_mul] using h⟩
  exact ⟨1, fun _ => i, fun _ => N, fun s => by simp [N]⟩

private theorem shift_re_pos {s t : ℂ} (h : -t.re < s.re) : 0 < (s + t).re := by
  rw [Complex.add_re]
  linarith

/-- All ordinary rank-one archimedean pair tests have entire normalizations.
For nonzero coefficient models a single Schwartz test has normalized value one. -/
def RankOneOrdinaryNormalizedTestsStatement : Prop :=
  (∀ (d e : List RealBlock), realRank d = 1 → realRank e = 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData 0),
      HasEntireOrdinaryNormalizations (realOrdinaryEqualTest 0 d e a D) (realPairLFactor d e) ∧
      (realWhittakerModel 0 d a ≠ ⊥ → realWhittakerModel 0 e (-a) ≠ ⊥ →
        HasFiniteOrdinaryNormalizationSum (realOrdinaryEqualTest 0 d e a D) (realPairLFactor d e))) ∧
  ∀ (d e : List ComplexCharacterData), d.length = 1 → e.length = 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData 0),
      HasEntireOrdinaryNormalizations (complexOrdinaryEqualTest 0 d e a D) (complexPairLFactor d e) ∧
      (complexWhittakerModel 0 d a ≠ ⊥ → complexWhittakerModel 0 e (-a) ≠ ⊥ →
        HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest 0 d e a D) (complexPairLFactor d e))

theorem rankOneOrdinaryNormalizedTests : RankOneOrdinaryNormalizedTestsStatement := by
  constructor
  · intro d e hd he a D
    obtain ⟨c, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hd
    obtain ⟨c', rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one he
    constructor
    · rintro ⟨W, W', Φ⟩
      obtain ⟨C, hW⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel W.2
      obtain ⟨C', hW'⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel W'.2
      obtain ⟨R, hR, hEq⟩ := RealRankZero.exists_normalized_realEqualIntegral D c c' hW hW' Φ
      exact normalization_of_denominator _ hR (realPairLFactor_denominator_ne_zero _ _)
        ⟨-(c.mul c').exponent.re, fun s hs => hEq s (shift_re_pos hs)⟩
    · intro hModel hModel'
      obtain ⟨W, hW, hW₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hModel
      obtain ⟨W', hW', hW₀'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hModel'
      obtain ⟨C, hC⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel hW
      obtain ⟨C', hC'⟩ := RealRankZero.exists_eq_of_mem_realWhittakerModel hW'
      have hC₀ : C ≠ 0 := fun hc => hW₀ (funext fun g => by simp [hC g, hc])
      have hC₀' : C' ≠ 0 := fun hc => hW₀' (funext fun g => by simp [hC' g, hc])
      obtain ⟨Φ, hΦ⟩ := RealRankZero.exists_realEqualIntegral_eq_LFactor D c c' hC hC' hC₀ hC₀'
      exact finiteNormalizationSum_of_exact _ _ (⟨W, hW⟩, ⟨W', hW'⟩, Φ)
        ⟨-(c.mul c').exponent.re, fun s hs => hΦ s (shift_re_pos hs)⟩
  · intro d e hd he a D
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp he
    constructor
    · rintro ⟨W, W', Φ⟩
      obtain ⟨C, hW⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel W.2
      obtain ⟨C', hW'⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel W'.2
      obtain ⟨R, hR, hEq⟩ := ComplexRankZero.exists_normalized_complexEqualIntegral D c c' hW hW' Φ
      exact normalization_of_denominator _ hR (complexPairLFactor_denominator_ne_zero _ _)
        ⟨-(c.mul c').exponent.re, fun s hs => hEq s (shift_re_pos hs)⟩
    · intro hModel hModel'
      obtain ⟨W, hW, hW₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hModel
      obtain ⟨W', hW', hW₀'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hModel'
      obtain ⟨C, hC⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW
      obtain ⟨C', hC'⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW'
      have hC₀ : C ≠ 0 := fun hc => hW₀ (funext fun g => by simp [hC g, hc])
      have hC₀' : C' ≠ 0 := fun hc => hW₀' (funext fun g => by simp [hC' g, hc])
      obtain ⟨Φ, hΦ⟩ := ComplexRankZero.exists_complexEqualIntegral_eq_LFactor D c c' hC hC' hC₀ hC₀'
      exact finiteNormalizationSum_of_exact _ _ (⟨W, hW⟩, ⟨W', hW'⟩, Φ)
        ⟨-(c.mul c').exponent.re, fun s hs => hΦ s (shift_re_pos hs)⟩

end Langlands.Global.RankinSelbergGlobal
