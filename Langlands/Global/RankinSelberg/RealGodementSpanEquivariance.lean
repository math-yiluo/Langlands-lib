import Langlands.Global.RankinSelberg.RealGodementSpanContinuation

/-! # Group covariance of the continued real Godement coefficients -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Set
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

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "ρ" => Whittaker.rightTranslation ℂ H

private theorem translatedSupport (q : H) (S : Set X) (hS : IsCompact S)
    (hRank : ∀ x ∈ S, HasFullRowRank x) (Φ : 𝓢(X, ℂ))
    (hSupport : ∀ x ∉ S, Φ x = 0) :
    ∃ T : Set X, IsCompact T ∧ (∀ x ∈ T, HasFullRowRank x) ∧
      ∀ x ∉ T, rectangularTranslate 1 q Φ x = 0 := by
  let e : X ≃ₜ X := Langlands.HarmonicAnalysis.rectangularHomeomorph q
  refine ⟨e ⁻¹' S, e.isCompact_preimage.mpr hS, ?_, ?_⟩
  · intro x hx
    obtain ⟨R, hR⟩ := hRank (e x) hx
    exact ⟨q.val * R, by rw [← Matrix.mul_assoc]; exact hR⟩
  · intro x hx
    rw [rectangularTranslate_apply, Units.val_one, Matrix.one_mul]
    exact hSupport _ hx

/-- The right translate of the section is a scalar times the section with the pulled-back test. -/
theorem sectionValue_rightTranslate (μ : Measure G) (c : RealCharacterData) (f : G → ℂ)
    (Φ : 𝓢(X, ℂ)) (q : H) :
    ρ q (sectionValue μ c f Φ) =
      determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) q • sectionValue μ c f (rectangularTranslate 1 q Φ) := by
  funext g
  let s := ((t + 1 : ℕ) : ℂ) / 2
  let v := (((t + 1 : ℕ) : ℂ) + 1) / 2
  change determinantWeight c s (g * q) *
      (∫ h, f h⁻¹ * determinantWeight c v h * Φ (rowPoint h.val (g * q)) ∂μ) =
    determinantWeight c s q * (determinantWeight c s g *
      (∫ h, f h⁻¹ * determinantWeight c v h * rectangularTranslate 1 q Φ (rowPoint h.val g) ∂μ))
  rw [map_mul, mul_left_comm (determinantWeight c s q), mul_assoc]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  dsimp only
  rw [rectangularTranslate_apply, Units.val_one, Matrix.one_mul]
  congr 1
  apply congrArg (⇑Φ)
  change h.val * (lastRows g.val * q.val) = (h.val * lastRows g.val) * q.val
  exact (Matrix.mul_assoc _ _ _).symm

/-- The column evaluation has the same right-translation scalar as the section. -/
theorem godementLeadingFamily_rightTranslate (D : RealQuotientMeasureData t) (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) (W : G → ℂ) (p : Fin 2) (g q : H) (z : ℂ) :
    godementLeadingFamily D a Φ W p (g * q) z =
      determinantWeight (charData p z) (((t + 1 : ℕ) : ℂ) / 2) q *
        godementLeadingFamily D a (rectangularTranslate 1 q Φ) W p g z := by
  let e := weylLong (t + 2) ℝ * g
  have hPullback : rectangularTranslate 1 (e * q) Φ =
      rectangularTranslate 1 e (rectangularTranslate 1 q Φ) := by
    ext x
    simp only [rectangularTranslate_apply, Units.val_one, Matrix.one_mul, Units.val_mul, Matrix.mul_assoc]
  have hShift : (((t + 1 : ℕ) : ℂ) / 2) = (((t : ℂ) + 1) / 2) := by push_cast; rfl
  simp only [godementLeadingFamily, godementColumnValue, ← mul_assoc (weylLong (t + 2) ℝ) g q,
    map_mul, hShift]
  rw [hPullback]
  ring

private theorem compactSectionSpan_right_mem (μ : Measure G) (c : RealCharacterData)
    (ds : List RealBlock) (q : H) :
    compactSectionSpan μ c ds ≤ (compactSectionSpan μ c ds).comap (ρ q) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f, S, φ, hf, hS, hRank, hSmooth, hSupport, rfl⟩
  let Φ := ofCompactSupport φ hSmooth S hS hSupport
  obtain ⟨T, hT, hTRank, hTZ⟩ := translatedSupport q S hS hRank Φ hSupport
  change ρ q (sectionValue μ c f Φ) ∈ compactSectionSpan μ c ds
  rw [sectionValue_rightTranslate]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨f, T, rectangularTranslate 1 q Φ, hf, hT, hTRank,
    (rectangularTranslate 1 q Φ).smooth ⊤, hTZ, rfl⟩

/-- Actual right translation restricted to the compact Godement section span. -/
def compactSectionRightTranslation (μ : Measure G) (c : RealCharacterData) (ds : List RealBlock)
    (q : H) : compactSectionSpan μ c ds →ₗ[ℂ] compactSectionSpan μ c ds :=
  ((ρ q).comp (compactSectionSpan μ c ds).subtype).codRestrict _ (fun F =>
    compactSectionSpan_right_mem μ c ds q F.property)

@[simp] theorem compactSectionRightTranslation_apply (μ : Measure G) (c : RealCharacterData)
    (ds : List RealBlock) (q : H) (F : compactSectionSpan μ c ds) (g : H) :
    (compactSectionRightTranslation μ c ds q F).val g = F.val (g * q) := rfl

/-- The left Whittaker law persists in the entire continued family. -/
theorem IsLeadingJacquetContinuation.leftWhittaker {a : ℝˣ} {p : Fin 2} {ds : List RealBlock}
    {F : H → ℂ} {A : ℂ → H → ℂ} (hA : IsLeadingJacquetContinuation a p ds F A)
    (u : GeneralLinear.upperUnipotent (t + 2) ℝ) (g : H) (z : ℂ) :
    A z (u.val * g) = realWhittakerCharacter (-a) u.val * A z g := by
  let z₀ : ℂ := ((realPositionExponent ds 0).re + 1 : ℝ)
  have hz₀ : (realPositionExponent ds 0).re < z₀.re := by
    simp only [z₀, Complex.ofReal_re]
    linarith
  have hLeft := hA.1 (u.val * g)
  have hRight := (hA.1 g).const_mul (realWhittakerCharacter (-a) u.val)
  have hEq : (fun z => A z (u.val * g)) = fun z => realWhittakerCharacter (-a) u.val * A z g := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hLeft.analyticAt z)
      (fun z _ => hRight.analyticAt z) (z₀ := z₀)
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀] with z hz
    rw [hA.2 z hz]
    exact realGodementOpenCellCovariance (t + 1) a _ u g
  exact congrFun hEq z

/-- Evaluating at the reference exponent gives a linear map on the compact section span
with the column formula, the right action and the left Whittaker law. -/
def RealGodementSpanEquivarianceStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock),
    IsStrictlyDominant (realPositionExponent ds) t → ∀ w : ℂ,
    let V := compactSectionSpan D.groupHaar (charData p w) ds
    ∃ J : V →ₗ[ℂ] (Langlands.GeneralLinear (t + 2) ℝ → ℂ),
      (∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
        (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S →
        (∀ x ∈ S, HasFullRowRank x) →
      ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)), (∀ x ∉ S, Φ x = 0) →
      ∀ F : V, F.val = sectionValue D.groupHaar (charData p w) f.val Φ → ∀ g,
        J F g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w) ∧
      (∀ q F, J (compactSectionRightTranslation D.groupHaar (charData p w) ds q F) =
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (t + 2) ℝ) q (J F)) ∧
      ∀ (F : V) (u : GeneralLinear.upperUnipotent (t + 2) ℝ) (g : Langlands.GeneralLinear (t + 2) ℝ),
        J F (u.val * g) = realWhittakerCharacter (-a) u.val * J F g

theorem realGodementSpanEquivariance : RealGodementSpanEquivarianceStatement := by
  intro t D a p ds hDom w V
  obtain ⟨L, hL, hGen⟩ := realGodementSpanContinuation t D a p ds hDom w
  let J := (LinearMap.proj w).comp L
  have hAction (q : Langlands.GeneralLinear (t + 2) ℝ) (F : V) :
      J (compactSectionRightTranslation D.groupHaar (charData p w) ds q F) =
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (t + 2) ℝ) q (J F) := by
    let σ := compactSectionRightTranslation D.groupHaar (charData p w) ds q
    let R := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (t + 2) ℝ) q
    obtain ⟨F, hF⟩ := F
    induction hF using Submodule.span_induction with
    | mem F hF =>
        let U : V := ⟨F, Submodule.subset_span hF⟩
        obtain ⟨f, S, φ, hf, hS, hRank, hSmooth, hSupport, he⟩ := hF
        let Φ := ofCompactSupport φ hSmooth S hS hSupport
        let Ψ := rectangularTranslate 1 q Φ
        let d := determinantWeight (charData p w) (((t + 1 : ℕ) : ℂ) / 2) q
        obtain ⟨T, hT, hTRank, hTZ⟩ := translatedSupport q S hS hRank Φ hSupport
        let Y : V := ⟨sectionValue D.groupHaar (charData p w) f Ψ,
          Submodule.subset_span ⟨f, T, Ψ, hf, hT, hTRank, Ψ.smooth ⊤, hTZ, rfl⟩⟩
        have hEq : σ U = d • Y := by
          apply Subtype.ext
          change R F = d • sectionValue D.groupHaar (charData p w) f Ψ
          rw [he]
          exact sectionValue_rightTranslate D.groupHaar (charData p w) f Φ q
        change J (σ U) = R (J U)
        rw [hEq, map_smul]
        funext g
        change d * L Y w g = L U w (g * q)
        have hY := hGen ⟨f, hf⟩ T hT hTRank Ψ hTZ Y rfl g
        have hU := hGen ⟨f, hf⟩ S hS hRank Φ hSupport U he (g * q)
        rw [hY, hU, godementLeadingFamily_rightTranslate]
    | zero =>
        change J (σ 0) = R (J 0)
        simp only [map_zero]
    | add F F' hF hF' ihF ihF' =>
        change J (σ (⟨F, hF⟩ + ⟨F', hF'⟩)) = R (J (⟨F, hF⟩ + ⟨F', hF'⟩))
        simp only [map_add]
        exact congrArg₂ (· + ·) ihF ihF'
    | smul c F hF ih =>
        change J (σ (c • ⟨F, hF⟩)) = R (J (c • ⟨F, hF⟩))
        simp only [map_smul]
        exact congrArg (c • ·) ih
  exact ⟨J, hGen, hAction, fun F u g => (hL F).leftWhittaker u g w⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
