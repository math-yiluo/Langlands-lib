import Langlands.Global.RankinSelberg.RealGodementFlatSection
import Langlands.Global.RankinSelberg.RealGodementFiniteGeneration
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # The real Jacquet continuation on the compact Godement span -/

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

open GramFormula PartialJacquet PrincipalSeriesExtension RealJacquetFrobenius

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

private def leadingCompactLinear (p : Fin 2) (ds : List RealBlock) (z : ℂ) :
    (H → ℂ) →ₗ[ℂ] (H → ℂ) :=
  (extensionLinear (shiftedExponent (t + 2)
    (realPositionExponent (.character (charData p z) :: ds)))).comp
    (LinearMap.pi fun k : Matrix.unitaryGroup (Fin (t + 2)) ℝ => LinearMap.proj (Unitary.toUnits k))

/-- An entire Jacquet continuation at fixed compact restriction. -/
def IsLeadingJacquetContinuation (a : ℝˣ) (p : Fin 2) (ds : List RealBlock)
    (F : H → ℂ) (A : ℂ → H → ℂ) : Prop :=
  (∀ g, Differentiable ℂ (fun z => A z g)) ∧
  ∀ z : ℂ, (realPositionExponent ds 0).re < z.re →
    A z = additiveJacquetIntegral a (leadingCompactVector p ds F z)

/-- Continuation at fixed compact restriction is pointwise unique. -/
theorem IsLeadingJacquetContinuation.unique {a : ℝˣ} {p : Fin 2} {ds : List RealBlock}
    {F : H → ℂ} {A B : ℂ → H → ℂ}
    (hA : IsLeadingJacquetContinuation a p ds F A) (hB : IsLeadingJacquetContinuation a p ds F B) :
    A = B := by
  let z₀ : ℂ := ((realPositionExponent ds 0).re + 1 : ℝ)
  have hz₀ : (realPositionExponent ds 0).re < z₀.re := by
    simp only [z₀, Complex.ofReal_re]
    linarith
  have hEq (g : H) : (fun z => A z g) = (fun z => B z g) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => (hA.1 g).analyticAt z)
      (fun z _ => (hB.1 g).analyticAt z) (z₀ := z₀)
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀] with z hz
    exact congrFun ((hA.2 z hz).trans (hB.2 z hz).symm) g
  exact funext fun z => funext fun g => congrFun (hEq g) z

private theorem exists_leadingContinuation (D : RealQuotientMeasureData t) (a : ℝˣ)
    (p : Fin 2) (ds : List RealBlock) (hDom : IsStrictlyDominant (realPositionExponent ds) t)
    (w : ℂ) :
    ∃ L : compactSectionSpan D.groupHaar (charData p w) ds →ₗ[ℂ] (ℂ → H → ℂ),
      (∀ F, IsLeadingJacquetContinuation a p ds F.val (L F)) ∧
      ∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
        (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
      ∀ (Φ : 𝓢(X, ℂ)), (∀ x ∉ S, Φ x = 0) →
      ∀ F, F.val = sectionValue D.groupHaar (charData p w) f.val Φ → ∀ g,
        L F w g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w := by
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let P (z : ℂ) := principalSeries ℝ (t + 2) (realPositionCharacter (.character (charData p z) :: ds))
  let V := compactSectionSpan μ (charData p w) ds
  have hV : V ≤ P w := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, S, Φ, hf, hS, hRank, hSmooth, hSupport, rfl⟩
    exact realGodementSection (t + 1) μ (charData p w) ds f hf S hS hRank Φ hSmooth hSupport
  let T (z : ℂ) : V →ₗ[ℂ] P z :=
    ((leadingCompactLinear p ds z).comp V.subtype).codRestrict _ (fun F =>
      leadingCompactVector_mem_principalSeries p ds (hV F.property) z)
  have hUpper (z : ℂ) (hz : (realPositionExponent ds 0).re < z.re) :
      IsStrictlyDominant (realPositionExponent (.character (charData p z) :: ds)) (t + 1) := by
    intro j hj
    cases j with
    | zero => exact hz
    | succ j => exact hDom j (Nat.lt_of_succ_lt_succ hj)
  let J (z : ℂ) (hz : (realPositionExponent ds 0).re < z.re) : V →ₗ[ℂ] (H → ℂ) :=
    (additiveJacquetLinear a (RealStrictCharacterLanglandsQuotient.isSignedPower _)
      (hUpper z hz)).comp (T z)
  have hGen (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
      (S : Set X) (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x)
      (Φ : 𝓢(X, ℂ)) (hSupport : ∀ x ∉ S, Φ x = 0)
      (F : V) (hF : F.val = sectionValue μ (charData p w) f.val Φ) :
      ∃ A : ℂ → H → ℂ, IsLeadingJacquetContinuation a p ds F.val A ∧
        ∀ g, A w g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w := by
    obtain ⟨Ψ, hΨw, hΨS, hSec, hDiff⟩ := realGodementFlatSection t D a p ds f hDom
      S hS hRank Φ hSupport w
    let A (z : ℂ) (g : H) := godementLeadingFamily D a (Ψ z) (additiveJacquetIntegral a f.val) p g z
    refine ⟨A, ⟨hDiff, ?_⟩, ?_⟩
    · intro z hz
      funext g
      have hEq := (realGodementSmoothLeading t D a p ds f hDom S hS hRank (Ψ z) (hΨS z) g).2 z hz
      rw [hSec z, ← hF] at hEq
      exact hEq
    · intro g
      change godementLeadingFamily D a (Ψ w) (additiveJacquetIntegral a f.val) p g w = _
      rw [hΨw]
  let HasCont (F : V) (A : ℂ → H → ℂ) := IsLeadingJacquetContinuation a p ds F.val A
  have hExists (F : V) : ∃ A : ℂ → H → ℂ, HasCont F A := by
    obtain ⟨F, hF⟩ := F
    induction hF using Submodule.span_induction with
    | mem F hF =>
        let U : V := ⟨F, Submodule.subset_span hF⟩
        obtain ⟨f, S, φ, hf, hS, hRank, hSmooth, hSupport, he⟩ := hF
        let Φ := ofCompactSupport φ hSmooth S hS hSupport
        obtain ⟨A, hA, _⟩ := hGen ⟨f, hf⟩ S hS hRank Φ hSupport U he
        exact ⟨A, hA⟩
    | zero =>
        refine ⟨0, fun _ => differentiable_const _, ?_⟩
        intro z hz
        exact ((J z hz).map_zero).symm
    | add F F' hF hF' ihF ihF' =>
        obtain ⟨A, hA⟩ := ihF
        obtain ⟨B, hB⟩ := ihF'
        refine ⟨A + B, fun g => (hA.1 g).add (hB.1 g), ?_⟩
        intro z hz
        change A z + B z = J z hz (⟨F, hF⟩ + ⟨F', hF'⟩)
        rw [(J z hz).map_add]
        exact congrArg₂ (· + ·) (hA.2 z hz) (hB.2 z hz)
    | smul c F hF ih =>
        obtain ⟨A, hA⟩ := ih
        refine ⟨c • A, fun g => (hA.1 g).const_smul c, ?_⟩
        intro z hz
        change c • A z = J z hz (c • ⟨F, hF⟩)
        rw [(J z hz).map_smul]
        exact congrArg (c • ·) (hA.2 z hz)
  let A (F : V) := Classical.choose (hExists F)
  have hA (F : V) : HasCont F (A F) := Classical.choose_spec (hExists F)
  let L : V →ₗ[ℂ] (ℂ → H → ℂ) := by
    refine { toFun := A, map_add' := ?_, map_smul' := ?_ }
    · intro F F'
      apply (hA (F + F')).unique
      refine ⟨fun g => ((hA F).1 g).add ((hA F').1 g), ?_⟩
      intro z hz
      change A F z + A F' z = J z hz (F + F')
      rw [(J z hz).map_add]
      exact congrArg₂ (· + ·) ((hA F).2 z hz) ((hA F').2 z hz)
    · intro c F
      apply (hA (c • F)).unique
      refine ⟨fun g => ((hA F).1 g).const_smul c, ?_⟩
      intro z hz
      change c • A F z = J z hz (c • F)
      rw [(J z hz).map_smul]
      exact congrArg (c • ·) ((hA F).2 z hz)
  refine ⟨L, hA, ?_⟩
  intro f S hS hRank Φ hSupport F hF g
  obtain ⟨B, hB, hBw⟩ := hGen f S hS hRank Φ hSupport F hF
  exact congrFun (congrFun ((hA F).unique hB) w) g |>.trans (hBw g)

/-- The compact Godement span has an entire linear Jacquet continuation with its stated
first-column evaluations on all compact test generators. -/
def RealGodementSpanContinuationStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock),
    IsStrictlyDominant (realPositionExponent ds) t → ∀ w : ℂ,
    ∃ L : compactSectionSpan D.groupHaar (charData p w) ds →ₗ[ℂ]
        (ℂ → Langlands.GeneralLinear (t + 2) ℝ → ℂ),
      (∀ F, IsLeadingJacquetContinuation a p ds F.val (L F)) ∧
      ∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
        (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S →
        (∀ x ∈ S, HasFullRowRank x) →
      ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)), (∀ x ∉ S, Φ x = 0) →
      ∀ F, F.val = sectionValue D.groupHaar (charData p w) f.val Φ → ∀ g,
        L F w g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w

theorem realGodementSpanContinuation : RealGodementSpanContinuationStatement := by
  intro t
  exact exists_leadingContinuation (t := t)

end Langlands.Global.RankinSelbergGlobal.RealGodement
