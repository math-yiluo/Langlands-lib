import Langlands.Global.RankinSelberg.RealGodementColumnParameter
import Langlands.Global.RankinSelberg.RealGodementCompactPicture
import Langlands.Global.RankinSelberg.RealGodementGramCutoff
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Compact real Godement tests realizing a fixed compact picture -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Set Matrix
open scoped ContDiff Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {m : ℕ}

local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "M" => Matrix (Fin m) (Fin m) ℝ

private theorem rowGram_det_ne_zero {x : X} (hx : HasFullRowRank x) : (rowGram x).det ≠ 0 := by
  obtain ⟨R, hR⟩ := hx
  have hInj : Function.Injective x.vecMul := by
    intro u v huv
    have he := congrArg (fun a => a ᵥ* R) huv
    simpa only [vecMul_vecMul, hR, vecMul_one] using he
  have hPos : (rowGram x).PosDef := by
    simpa only [rowGram, conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self x hInj
  exact hPos.det_pos.ne'

private theorem exists_smooth_gramLog {S : Set X} (hS : IsCompact S)
    (hRank : ∀ x ∈ S, HasFullRowRank x) :
    ∃ b : X → ℂ, ContDiff ℝ ∞ b ∧ ∀ x ∈ S, b x = -(Real.log |(rowGram x).det| : ℂ) / 2 := by
  have hDetM : ContDiff ℝ ∞ (Matrix.det : M → ℝ) :=
    PrincipalSeriesExtension.contDiff_det_comp PrincipalSeriesExtension.contDiff_entry
  have hDet : ContDiff ℝ ∞ (fun x : X => (rowGram x).det) :=
    hDetM.comp (contDiff_rowGram (m := m))
  let V : Set X := {x | (rowGram x).det ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun hDet.continuous continuous_const
  have hSV : S ⊆ V := fun x hx => rowGram_det_ne_zero (hRank x hx)
  obtain ⟨U, hU, hSU, hUV⟩ := hS.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hSV)
  obtain ⟨χ, hχ, _, hSupport, hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU hS.isClosed hSU
  let b (x : X) := -(χ x : ℂ) * (Real.log |(rowGram x).det| : ℂ) / 2
  refine ⟨b, ?_, fun x hx => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ V
    · have hDetx : (rowGram x).det ≠ 0 := hx
      have hAbsAt : ContDiffAt ℝ ∞ (fun y : ℝ => |y|) (rowGram x).det :=
        contDiffAt_abs hDetx
      have hAbs : ContDiffAt ℝ ∞ (fun y => |(rowGram y).det|) x := by
        simpa only [Function.comp_apply, Function.comp_def] using
          hAbsAt.comp x (hDet.contDiffAt (x := x))
      have hLog := hAbs.log (abs_ne_zero.mpr hDetx)
      exact (((Complex.ofRealCLM.contDiff.comp hχ).contDiffAt.neg).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp x hLog)).div_const 2
    · have hxU : x ∉ closure U := fun h => hx (hUV h)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_closure.isOpen_compl).mem_nhds hxU] with y hy
      have hχy : χ y = 0 := by
        by_contra hz
        exact hy (subset_closure (hSupport ▸ hz))
      simp only [b, hχy, Complex.ofReal_zero, neg_zero, zero_mul, zero_div]
  · simp only [b, (hOne x).mp hx, Complex.ofReal_one, neg_mul, one_mul]

private theorem log_rowGram_rowPoint_orthogonal (h : G) {k : H} (hk : k ∈ unitaryCompact ℝ (m + 1)) :
    Real.log |(rowGram (rowPoint h.val k)).det| = 2 * Real.log |h.val.det| := by
  have hDet : |h.val.det| ≠ 0 := abs_ne_zero.mpr (determinant h).ne_zero
  rw [rowGram_rowPoint_of_orthogonal h.val hk, det_mul, det_transpose, abs_mul,
    Real.log_mul hDet hDet, two_mul]

private theorem section_exponentialTest_eqOn [MeasurableSpace G] (μ : Measure G)
    (p : Fin 2) (w z : ℂ) (f : G → ℂ) (Φ : 𝓢(X, ℂ)) (S : Set X) (hS : IsCompact S)
    (hSupport : ∀ x ∉ S, Φ x = 0) (b : X → ℂ) (hb : ContDiff ℝ ∞ b)
    (hLog : ∀ x ∈ S, b x = -(Real.log |(rowGram x).det| : ℂ) / 2) :
    EqOn (sectionValue μ (charData p z) f (exponentialTest b hb Φ S hS hSupport (z - w)))
      (sectionValue μ (charData p w) f Φ) (unitaryCompact ℝ (m + 1)) := by
  intro k hk
  let u := (m : ℂ) / 2
  let v := ((m : ℂ) + 1) / 2
  change determinantWeight (charData p z) u k *
      (∫ h, f h⁻¹ * determinantWeight (charData p z) v h *
        exponentialTest b hb Φ S hS hSupport (z - w) (rowPoint h.val k) ∂μ) =
    determinantWeight (charData p w) u k *
      (∫ h, f h⁻¹ * determinantWeight (charData p w) v h * Φ (rowPoint h.val k) ∂μ)
  have hWeight : determinantWeight (charData p z) u k = determinantWeight (charData p w) u k := by
    rw [determinantWeight_exponent_shift _ _ _ w,
      MaximalParabolicIntegration.abs_det_unitary ⟨k, hk⟩]
    simp
  rw [hWeight]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  dsimp only
  rw [exponentialTest_apply]
  by_cases hx : rowPoint h.val k ∈ S
  · have hExp : (z - w) * b (rowPoint h.val k) = -((z - w) * (Real.log |h.val.det| : ℂ)) := by
      rw [hLog _ hx, log_rowGram_rowPoint_orthogonal h hk]
      push_cast
      ring
    rw [determinantWeight_exponent_shift _ _ _ w h, hExp]
    let a := (z - w) * (Real.log |h.val.det| : ℂ)
    have he : Complex.exp a * Complex.exp (-a) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc
      _ = f h⁻¹ * determinantWeight (charData p w) v h *
          Φ (rowPoint h.val k) * (Complex.exp a * Complex.exp (-a)) := by dsimp only [a]; ring
      _ = _ := by rw [he, mul_one]
  · simp only [hSupport _ hx, mul_zero]

/-- A compact section can be kept fixed on the orthogonal group while varying its leading
exponent, with entire first-column values for strictly dominant lower data. -/
def RealGodementFlatSectionStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock)
    (f : principalSeries ℝ (t + 1) (realPositionCharacter ds)),
    IsStrictlyDominant (realPositionExponent ds) t →
    ∀ (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S →
      (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)), (∀ x ∉ S, Φ x = 0) →
    ∀ w : ℂ,
      let F := sectionValue D.groupHaar (charData p w) f.val Φ
      ∃ Ψ : ℂ → 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ),
        Ψ w = Φ ∧ (∀ z x, x ∉ S → Ψ z x = 0) ∧
        (∀ z, sectionValue D.groupHaar (charData p z) f.val (Ψ z) = leadingCompactVector p ds F z) ∧
        (∀ g, Differentiable ℂ (fun z => godementLeadingFamily D a (Ψ z)
          (additiveJacquetIntegral a f.val) p g z))

theorem realGodementFlatSection : RealGodementFlatSectionStatement := by
  intro t D a p ds f hDom S hS hRank Φ hSupport w F
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  obtain ⟨b, hb, hLog⟩ := exists_smooth_gramLog hS hRank
  let Ψ (z : ℂ) := exponentialTest b hb Φ S hS hSupport (z - w)
  have hΨ (z) (x) (hx : x ∉ S) : Ψ z x = 0 := by
    simp only [Ψ, exponentialTest_apply, hSupport x hx, mul_zero]
  have hΨw : Ψ w = Φ := by
    ext x
    simp only [Ψ, sub_self, exponentialTest_apply, zero_mul, Complex.exp_zero, one_mul]
  have hMem (z : ℂ) : sectionValue μ (charData p z) f.val (Ψ z) ∈
      principalSeries ℝ (t + 2) (realPositionCharacter (.character (charData p z) :: ds)) :=
    realGodementSection (t + 1) μ (charData p z) ds f.val f.property S hS hRank (Ψ z)
      ((Ψ z).smooth ⊤) (hΨ z)
  have hF : F ∈ principalSeries ℝ (t + 2) (realPositionCharacter (.character (charData p w) :: ds)) := by
    simpa only [hΨw] using hMem w
  have hSec (z : ℂ) : sectionValue μ (charData p z) f.val (Ψ z) = leadingCompactVector p ds F z := by
    apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries (hMem z)
      (leadingCompactVector_mem_principalSeries p ds hF z)
    exact (section_exponentialTest_eqOn μ p w z f.val Φ S hS hSupport b hb hLog).trans
      (compactPictureExtension_eqOn _ F).symm
  refine ⟨Ψ, hΨw, hΨ, hSec, fun g => ?_⟩
  let Φ₀ := Ψ 0
  have h₀ (x) (hx : x ∉ S) : Φ₀ x = 0 := hΨ 0 x hx
  have hExpo (z : ℂ) : Ψ z = exponentialTest b hb Φ₀ S hS h₀ z := by
    ext x
    simp only [Ψ, Φ₀, exponentialTest_apply, zero_sub, sub_mul, neg_mul, Complex.exp_sub,
      Complex.exp_neg, div_eq_mul_inv, mul_assoc]
  obtain ⟨hReg, hGrowth⟩ := regular_additiveJacquetIntegral a hDom f
  simp_rw [hExpo]
  exact realGodementColumnParameter t D a p _ hReg hGrowth g b hb Φ₀ S hS h₀

end Langlands.Global.RankinSelbergGlobal.RealGodement
