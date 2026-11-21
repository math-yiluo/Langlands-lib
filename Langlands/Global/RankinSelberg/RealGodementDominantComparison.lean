import Langlands.Global.RankinSelberg.RealGodementSchwartzJoint
import Langlands.Global.RankinSelberg.RealGodementUniformModel

/-! # The continued real coefficient in the convergent leading chamber -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator SchwartzMap

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

/-- In the convergent leading chamber the continued map is the open-cell Jacquet
integral. In the Schwartz joint convergence range it gives the column formula on
any Schwartz Godement section belonging to its source. -/
def RealGodementDominantComparisonStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock),
    IsStrictlyDominant (realPositionExponent ds) t → ∀ w : ℂ,
    (realPositionExponent ds 0).re < w.re →
    let c := charData p w
    let V := compactSectionSpan D.groupHaar c ds
    ∃ J : V →ₗ[ℂ] (H → ℂ),
      IsRealUniformWhittakerIntertwiner (t + 1) (.character c :: ds) (-a)
        (J.comp (compactSectionKFiniteInclusion D c ds)) ∧
      (∀ F, J F = additiveJacquetIntegral a F.val) ∧
      ((∀ i : Fin (t + 1), ((t + 1 : ℕ) : ℝ) + normExponent (realPositionExponent ds) (t + 1) i ≤
        w.re + (((t + 1 : ℕ) : ℝ) + 1) / 2) →
      ∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds)) (Φ : 𝓢(X, ℂ)) (F : V),
        F.val = sectionValue D.groupHaar c f.val Φ → ∀ g,
          J F g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w)

theorem realGodementDominantComparison : RealGodementDominantComparisonStatement (t := t) := by
  intro D a p ds hDom w hw c V
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  have hUpper : IsStrictlyDominant (realPositionExponent (.character c :: ds)) (t + 1) := by
    intro j hj
    cases j with
    | zero => exact hw
    | succ j => exact hDom j (Nat.lt_of_succ_lt_succ hj)
  obtain ⟨J, hJ, hGen⟩ := realGodementUniformModel D a p ds hDom w
  let ι := Submodule.inclusion (compactSectionSpan_le_principalSeries μ c ds)
  let A := (additiveJacquetLinear a (RealStrictCharacterLanglandsQuotient.isSignedPower _) hUpper).comp ι
  let G₀ : Set (H → ℂ) := {F | ∃ (f : G → ℂ) (S : Set X) (φ : X → ℂ),
    f ∈ principalSeries ℝ (t + 1) (realPositionCharacter ds) ∧ IsCompact S ∧
    (∀ x ∈ S, HasFullRowRank x) ∧ ContDiff ℝ ∞ φ ∧ (∀ x ∉ S, φ x = 0) ∧
    F = sectionValue μ c f φ}
  let E : Set V := (Subtype.val : V → H → ℂ) ⁻¹' G₀
  have hSpan : Submodule.span ℂ E = ⊤ := Submodule.span_span_coe_preimage
  have hEq : Set.EqOn J A E := by
    intro F hF
    obtain ⟨f, S, φ, hf, hS, hR, hφ, hZero, he⟩ := hF
    let Φ := ofCompactSupport φ hφ S hS hZero
    funext g
    rw [hGen ⟨f, hf⟩ S hS hR Φ hZero F he]
    change _ = additiveJacquetIntegral a F.val g
    rw [he]
    exact (realGodementSmoothLeading t D a p ds ⟨f, hf⟩ hDom S hS hR Φ hZero g).2 w hw
  have hValue (F : V) : J F = additiveJacquetIntegral a F.val :=
    LinearMap.eqOn_span hEq (hSpan.symm ▸ Submodule.mem_top)
  refine ⟨J, hJ, hValue, fun hStrip f Φ F hF g => ?_⟩
  rw [hValue, hF]
  exact (realGodementSchwartzJoint t D a c ds f.val f.property hUpper hStrip Φ g).2

end Langlands.Global.RankinSelbergGlobal.RealGodement
