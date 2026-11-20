import Langlands.Global.RankinSelberg.ComplexGodementCofactorTest
import Langlands.Global.RankinSelberg.ComplexGodementCompactPairing
import Langlands.Global.RankinSelberg.ComplexGodementCutoffNeighborhood
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Separation at identity by compact Godement sections -/

noncomputable section

open MeasureTheory Matrix Set
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "H" => Langlands.GeneralLinear n ℂ
local notation "G" => Langlands.GeneralLinear (n + 1) ℂ
local notation "K₀" => Matrix.unitaryGroup (Fin n) ℂ
local notation "K" => unitaryCompact ℂ (n + 1)
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ
local notation "Square" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
local notation "E" => trailingRows (1 : Square)

local instance compactSeparationGLMeasure (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear m ℂ) := borel _
local instance compactSeparationGLBorel (m : ℕ) : BorelSpace (Langlands.GeneralLinear m ℂ) := ⟨rfl⟩
local instance compactSeparationGLFirstCountable (m : ℕ) : FirstCountableTopology (Langlands.GeneralLinear m ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.firstCountableTopology
local instance compactSeparationGLSecondCountable (m : ℕ) : SecondCountableTopology (Langlands.GeneralLinear m ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance compactSeparationUnitaryMeasure (m : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Fin m) ℂ) :=
  borel _
local instance compactSeparationUnitaryBorel (m : ℕ) : BorelSpace (Matrix.unitaryGroup (Fin m) ℂ) := ⟨rfl⟩

/-- The cutoff hypotheses used to construct smooth compact full-row-rank cofactor tests. -/
def IsGodementCofactorCutoff (χ : 𝓢(Rect, ℂ)) : Prop :=
  HasCompactSupport χ ∧ (∀ X ∈ tsupport χ, IsUnit (specialCompletion X)) ∧
    (∀ X ∈ unitaryTrailingRows n, χ X = 1) ∧ (∀ (X : Rect) (k : K), χ (X * k.val.val) = χ X)

theorem IsGodementCofactorCutoff.cofactorTest_regular {χ : 𝓢(Rect, ℂ)} (hχ : IsGodementCofactorCutoff χ)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) {f : G → ℂ}
    (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) :
    ContDiff ℝ ∞ (cofactorTest χ f) ∧ HasCompactSupport (cofactorTest χ f) ∧
      ∀ X ∈ tsupport (cofactorTest χ f), HasFullRowRank X := by
  obtain ⟨Φ, hΦ, hc, hfull, _⟩ := complexGodementCofactorTest χ hχ.1 hχ.2.1 hχ.2.2.2 d ds f hf
  simpa only [hΦ] using And.intro (Φ.smooth ⊤) (And.intro hc hfull)

private def mulCutoff (χ ψ : 𝓢(Rect, ℂ)) (hc : HasCompactSupport χ) : 𝓢(Rect, ℂ) :=
  (hc.mul_right (f' := (ψ : Rect → ℂ))).toSchwartzMap ((χ.smooth ⊤).mul (ψ.smooth ⊤))

private theorem mulCutoff_apply (χ ψ : 𝓢(Rect, ℂ)) (hc : HasCompactSupport χ) (X : Rect) :
    mulCutoff χ ψ hc X = χ X * ψ X := rfl

private theorem IsGodementCofactorCutoff.mul {χ ψ : 𝓢(Rect, ℂ)}
    (hχ : IsGodementCofactorCutoff χ) (hψ : IsGodementCofactorCutoff ψ) :
    IsGodementCofactorCutoff (mulCutoff χ ψ hχ.1) := by
  have h : (mulCutoff χ ψ hχ.1 : Rect → ℂ) = (χ : Rect → ℂ) * (ψ : Rect → ℂ) := rfl
  refine ⟨h ▸ hχ.1.mul_right, ?_, ?_, ?_⟩
  · rw [h]
    exact fun X hX => hχ.2.1 X (tsupport_mul_subset_left hX)
  · intro X hX
    rw [mulCutoff_apply, hχ.2.2.1 X hX, hψ.2.2.1 X hX, one_mul]
  · intro X k
    rw [mulCutoff_apply, mulCutoff_apply, hχ.2.2.2 X k, hψ.2.2.2 X k]

private def compactRightAverage (B : H → ℂ) (h : H) : ℂ :=
  ∫ k : K₀, B (h * Unitary.toUnits k) ∂compactMatrixHaar n

private theorem continuous_compactRightAverage {B : H → ℂ} (hB : Continuous B) :
    Continuous (compactRightAverage B) := by
  have hc : Continuous (Function.uncurry (fun (h : H) (k : K₀) => B (h * Unitary.toUnits k))) :=
    hB.comp (continuous_fst.mul (continuous_unitary_toUnits.comp continuous_snd))
  change Continuous (fun h : H => ∫ k : K₀, B (h * Unitary.toUnits k) ∂compactMatrixHaar n)
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := compactMatrixHaar n) hc isCompact_univ

private theorem compactRightAverage_at_unitary (B : H → ℂ) {h : H} (hh : h ∈ unitaryCompact ℂ n) :
    compactRightAverage B h = compactRightAverage B 1 := by
  let k : K₀ := ⟨h.val, hh⟩
  have hk : Unitary.toUnits k = h := Units.ext rfl
  unfold compactRightAverage
  simp only [one_mul, ← hk, ← map_mul]
  exact integral_mul_left_eq_self (fun k' : K₀ => B (Unitary.toUnits k')) k

private theorem compactRightAverage_support_integral (ν : Measure H) [IsLocallyFiniteMeasure ν]
    [ν.IsMulRightInvariant] {B : H → ℂ} (hB : Continuous B) (hBc : HasCompactSupport B) :
    HasCompactSupport (compactRightAverage B) ∧
      (∫ h, compactRightAverage B h ∂ν) = ∫ h, B h ∂ν := by
  let F : H × K₀ → ℂ := fun p => B (p.1 * Unitary.toUnits p.2)
  let L := (fun p : H × K₀ => (p.1 * (Unitary.toUnits p.2)⁻¹, p.2)) '' (tsupport B ×ˢ (univ : Set K₀))
  have hL : IsCompact L := (hBc.prod isCompact_univ).image
    ((continuous_fst.mul (continuous_unitary_toUnits.comp continuous_snd).inv).prodMk continuous_snd)
  have hFsub : Function.support F ⊆ L := by
    intro p hp
    refine ⟨(p.1 * Unitary.toUnits p.2, p.2), ⟨subset_tsupport _ hp, mem_univ _⟩, ?_⟩
    exact Prod.ext (mul_inv_cancel_right _ _) rfl
  have hFi : Integrable F (ν.prod (compactMatrixHaar n)) :=
    (hB.comp (continuous_fst.mul (continuous_unitary_toUnits.comp continuous_snd))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hL hFsub)
  constructor
  · apply HasCompactSupport.of_support_subset_isCompact (hL.image continuous_fst)
    intro h hh
    by_contra hn
    apply hh
    apply integral_eq_zero_of_ae
    filter_upwards with k
    by_contra hm
    exact hn ⟨(h, k), hFsub hm, rfl⟩
  · calc
      (∫ h, compactRightAverage B h ∂ν) = ∫ k : K₀, ∫ h, F (h, k) ∂ν ∂compactMatrixHaar n :=
        integral_integral_swap hFi
      _ = _ := by
        have h (k : K₀) : (∫ h, F (h, k) ∂ν) = ∫ h, B h ∂ν :=
          integral_mul_right_eq_self B (Unitary.toUnits k)
        simp only [h, integral_const, probReal_univ, one_smul]

private theorem trailingIdentity_mul_unitary (h : H) (k : K₀) :
    (h * Unitary.toUnits k).val * E = (h.val * E) * (trailingBlockGL (Unitary.toUnits k)).val := by
  rw [Units.val_mul, Matrix.mul_assoc, ← trailingBlock_trailingRows, ← trailingBlockGL_val]
  have hr : E * (trailingBlockGL (Unitary.toUnits k)).val =
      trailingRows (trailingBlockGL (Unitary.toUnits k)).val := by
    change (1 : Square).submatrix Fin.succ id * (trailingBlockGL (Unitary.toUnits k)).val =
      (trailingBlockGL (Unitary.toUnits k)).val.submatrix Fin.succ id
    simpa only [Matrix.one_mul, Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul (1 : Square) (trailingBlockGL (Unitary.toUnits k)).val
        Fin.succ id id Function.bijective_id).symm
  rw [← hr, Matrix.mul_assoc]

private theorem cofactorIntegrand_unitary (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {χ : 𝓢(Rect, ℂ)} (hχ : IsGodementCofactorCutoff χ) {f : G → ℂ}
    (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) (f₀ : H → ℂ) (k : K₀) :
    godementSectionIntegrand d (cofactorTest χ f) f₀ 1 (Unitary.toUnits k) =
      f (trailingBlockGL (Unitary.toUnits k)) * f₀ (Unitary.toUnits k⁻¹) := by
  let k' : K := ⟨trailingBlockGL (Unitary.toUnits k), trailingBlockGL_mem_unitary k.2⟩
  have hr : (Unitary.toUnits k).val * E = trailingRows k'.val.val :=
    (trailingBlock_trailingRows _).symm
  have hw : characterWeight d (((n : ℂ) + 1) / 2) (determinant (Unitary.toUnits k)) =
      (d.character (determinant (Unitary.toUnits k)) : ℂ) := by
    have hN := normSqC_det_unitary (⟨Unitary.toUnits k, k.2⟩ : unitaryCompact ℂ n)
    change normSqC (determinant (Unitary.toUnits k) : ℂ) = 1 at hN
    change (d.character (determinant (Unitary.toUnits k)) : ℂ) *
      normSqC (determinant (Unitary.toUnits k) : ℂ) ^ (((n : ℂ) + 1) / 2) = _
    rw [hN, Complex.one_cpow, mul_one]
  unfold godementSectionIntegrand
  rw [Units.val_one, hr, cofactorTest_unitaryTrailingRows χ hχ.2.2.2 hχ.2.2.1 d ds f hf k', hw, ← map_inv]
  change _ * f k'.val * f₀ (Unitary.toUnits k⁻¹) * _ = f k'.val * f₀ (Unitary.toUnits k⁻¹)
  have hk : determinant k'.val = determinant (Unitary.toUnits k) := determinant_trailingBlockGL _
  rw [hk]
  let z : ℂ := d.character (determinant (Unitary.toUnits k))
  change z⁻¹ * f k'.val * f₀ (Unitary.toUnits k⁻¹) * z = _
  calc
    _ = (z⁻¹ * z) * (f k'.val * f₀ (Unitary.toUnits k⁻¹)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (d.character (determinant (Unitary.toUnits k))).ne_zero, one_mul]

private def cofactorIntegrand (d : ComplexCharacterData) (χ : 𝓢(Rect, ℂ)) (f : G → ℂ) (f₀ : H → ℂ) :
    H → ℂ := godementSectionIntegrand d (cofactorTest χ f) f₀ 1

private theorem cofactorIntegrand_regular (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {χ : 𝓢(Rect, ℂ)} (hχ : IsGodementCofactorCutoff χ) {f : G → ℂ}
    (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) {f₀ : H → ℂ} (hf₀ : Continuous f₀) :
    Continuous (cofactorIntegrand d χ f f₀) ∧ HasCompactSupport (cofactorIntegrand d χ f f₀) := by
  obtain ⟨hΦ, hΦc, hΦfull⟩ := hχ.cofactorTest_regular d ds hf
  constructor
  · have hc := continuous_godementSectionIntegrand (m := n) d (Φ := cofactorTest χ f) hΦ.continuous hf₀
    let i : H → G × H := fun h => (1, h)
    have hi : Continuous i := continuous_const.prodMk continuous_id
    have heq : Function.uncurry (godementSectionIntegrand d (cofactorTest χ f) f₀) ∘ i =
        cofactorIntegrand d χ f f₀ := rfl
    rw [← heq]
    exact hc.comp hi
  · exact hasCompactSupport_godementSectionIntegrand (m := n) d (Φ := cofactorTest χ f) hΦc hΦfull f₀ 1

private theorem cofactorIntegrand_mulCutoff (d : ComplexCharacterData) (χ ψ : 𝓢(Rect, ℂ))
    (hc : HasCompactSupport χ) (f : G → ℂ) (f₀ : H → ℂ) (h : H) :
    cofactorIntegrand d (mulCutoff χ ψ hc) f f₀ h = χ (h.val * E) * cofactorIntegrand d ψ f f₀ h := by
  simp only [cofactorIntegrand, godementSectionIntegrand, Units.val_one]
  have hEval (ξ : 𝓢(Rect, ℂ)) (X : Rect) :
      cofactorTest ξ f X = ξ X * unitsExtension f (specialCompletion X) := rfl
  simp only [hEval, mulCutoff_apply]
  ring

private theorem compactRightAverage_mulCutoff (d : ComplexCharacterData) (χ ψ : 𝓢(Rect, ℂ))
    (hχ : IsGodementCofactorCutoff χ) (f : G → ℂ) (f₀ : H → ℂ) (h : H) :
    compactRightAverage (cofactorIntegrand d (mulCutoff χ ψ hχ.1) f f₀) h =
      χ (h.val * E) * compactRightAverage (cofactorIntegrand d ψ f f₀) h := by
  unfold compactRightAverage
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with k
  rw [cofactorIntegrand_mulCutoff, trailingIdentity_mul_unitary]
  let k' : K := ⟨trailingBlockGL (Unitary.toUnits k), trailingBlockGL_mem_unitary k.2⟩
  exact congrArg (fun z => z * cofactorIntegrand d ψ f f₀ (h * Unitary.toUnits k)) (hχ.2.2.2 _ k')

private theorem cofactorIntegrand_positive (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) {f : G → ℂ}
    (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) {f₀ : H → ℂ} (hf₀ : Continuous f₀)
    {ψ : 𝓢(Rect, ℂ)} (hψ : IsGodementCofactorCutoff ψ)
    (hpos : 0 < (compactRightAverage (cofactorIntegrand d ψ f f₀) 1).re) :
    ∃ χ : 𝓢(Rect, ℂ), IsGodementCofactorCutoff χ ∧ 0 < (∫ h, cofactorIntegrand d χ f f₀ h ∂ν).re := by
  let B := cofactorIntegrand d ψ f f₀
  have hB := (cofactorIntegrand_regular d ds hψ hf hf₀).1
  let V : Set H := {h | 0 < (compactRightAverage B h).re}
  have hV : IsOpen V := isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_compactRightAverage hB))
  have hVsub : (unitaryCompact ℂ n : Set H) ⊆ V := fun h hh => by
    change 0 < (compactRightAverage B h).re
    rw [compactRightAverage_at_unitary B hh]
    exact hpos
  obtain ⟨U, hU, hUsub, hUinv, hUV⟩ := complexGodementCutoffNeighborhood V hV hVsub
  obtain ⟨χ₁, hχ₁c, hχ₁sub, hχ₁u, hχ₁one, hχ₁inv, hχ₁range⟩ := exists_cofactorTestCutoff U hU hUsub hUinv
  have hχ₁ : IsGodementCofactorCutoff χ₁ := ⟨hχ₁c, hχ₁u, hχ₁one, hχ₁inv⟩
  let χ := mulCutoff χ₁ ψ hχ₁c
  have hχ : IsGodementCofactorCutoff χ := hχ₁.mul hψ
  let D := cofactorIntegrand d χ f f₀
  obtain ⟨hD, hDc⟩ := cofactorIntegrand_regular d ds hχ hf hf₀
  have hEq (h : H) : compactRightAverage D h = χ₁ (h.val * E) * compactRightAverage B h :=
    compactRightAverage_mulCutoff d χ₁ ψ hχ₁ f f₀ h
  have hnonneg (h : H) : 0 ≤ (compactRightAverage D h).re := by
    rw [hEq]
    by_cases hz : χ₁ (h.val * E) = 0
    · simp [hz]
    have hVh : h ∈ V := hUV h (hχ₁sub (subset_tsupport χ₁ hz))
    obtain ⟨r, hr, hrEq⟩ := hχ₁range (h.val * E)
    rw [hrEq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hr.1 (le_of_lt hVh)
  have hnonzero : (compactRightAverage D 1).re ≠ 0 := by
    have h1 : χ₁ E = 1 := hχ₁one _ ⟨1, rfl⟩
    rw [hEq, Units.val_one, Matrix.one_mul, h1, one_mul]
    exact hpos.ne'
  obtain ⟨hAc, hAI⟩ := compactRightAverage_support_integral ν hD hDc
  have hA := continuous_compactRightAverage hD
  have hposInt := (Complex.continuous_re.comp hA).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hAc.comp_left Complex.zero_re) hnonneg hnonzero (μ := ν)
  change 0 < ∫ h, RCLike.re (compactRightAverage D h) ∂ν at hposInt
  rw [integral_re (hA.integrable_of_hasCompactSupport hAc), hAI] at hposInt
  exact ⟨χ, hχ, hposInt⟩

/-- A larger compact-finite vector nonzero at identity yields a cofactor test with a strictly
positive real Godement section value at identity against a suitable smaller standard vector. -/
def ComplexGodementCompactSeparationStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData) (f : G → ℂ),
    f ∈ kFiniteFunctions (complexStandardModule (n + 1) (d :: List.ofFn es)) K → f 1 ≠ 0 →
    ∃ (χ : 𝓢(Rect, ℂ)) (f₀ : H → ℂ), IsGodementCofactorCutoff χ ∧
      f₀ ∈ kFiniteFunctions (complexStandardModule n (List.ofFn es)) (unitaryCompact ℂ n) ∧
      0 < (godementSection ν d (cofactorTest χ f) f₀ 1).re

theorem complexGodementCompactSeparation : ComplexGodementCompactSeparationStatement (n := n) := by
  intro ν hν hνr d es f hf hf₁
  let ds := List.ofFn es
  have hfS : f ∈ complexStandardModule (n + 1) (d :: ds) := hf.1
  obtain ⟨f₀, hf₀, hpair⟩ := complexGodementCompactPairing d es f hf hf₁
  have hf₀c : Continuous f₀ := hf₀.1.1.continuous
  obtain ⟨ψ, hψc, _, hψu, hψone, hψinv, _⟩ := exists_cofactorTestCutoff (n := n) univ
    isOpen_univ (subset_univ _) (fun _ _ _ => mem_univ _)
  have hψ : IsGodementCofactorCutoff ψ := ⟨hψc, hψu, hψone, hψinv⟩
  have hpos : 0 < (compactRightAverage (cofactorIntegrand d ψ f f₀) 1).re := by
    have h (k : K₀) : cofactorIntegrand d ψ f f₀ (Unitary.toUnits k) =
        f (trailingBlockGL (Unitary.toUnits k)) * f₀ (Unitary.toUnits k⁻¹) :=
      cofactorIntegrand_unitary d ds hψ hfS f₀ k
    simp only [compactRightAverage, one_mul, h]
    exact hpair
  obtain ⟨χ, hχ, hχpos⟩ := cofactorIntegrand_positive ν d ds hfS hf₀c hψ hpos
  refine ⟨χ, f₀, hχ, hf₀, ?_⟩
  simpa only [godementSection, cofactorIntegrand, map_one, one_mul] using hχpos

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
