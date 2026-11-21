import Langlands.Analysis.SchwartzCompactFamilies
import Langlands.Global.RankinSelberg.RealGodementColumnGrowth
import Langlands.Global.RankinSelberg.RealGodementFiniteGeneration

/-! # A shared polynomial growth exponent on the real compact Godement span -/

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

/-- A linear Godement evaluation has a common height exponent on the whole span if it
agrees with the column values on the compact section generators. -/
def RealGodementSpanGrowthStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock),
    IsStrictlyDominant (realPositionExponent ds) t → ∀ w : ℂ,
    let V := compactSectionSpan D.groupHaar (charData p w) ds
    ∃ M : ℕ, ∀ J : V →ₗ[ℂ] (Langlands.GeneralLinear (t + 2) ℝ → ℂ),
      (∀ (f : principalSeries ℝ (t + 1) (realPositionCharacter ds))
          (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S →
          (∀ x ∈ S, HasFullRowRank x) →
        ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)), (∀ x ∉ S, Φ x = 0) →
        ∀ F : V, F.val = sectionValue D.groupHaar (charData p w) f.val Φ → ∀ g,
          J F g = godementLeadingFamily D a Φ (additiveJacquetIntegral a f.val) p g w) →
      ∀ F : V, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖J F g‖ ≤ C * realMatrixHeight g ^ M

theorem realGodementSpanGrowth : RealGodementSpanGrowthStatement := by
  intro t D a p ds hDom w V
  obtain ⟨N, hN⟩ := exists_commonGrowth_additiveJacquetIntegral a hDom
  obtain ⟨M, hM⟩ := realGodementColumnGrowth t D a p w N
  refine ⟨M, fun J hJ F => ?_⟩
  obtain ⟨F, hF⟩ := F
  induction hF using Submodule.span_induction with
  | mem F hF =>
      let U : V := ⟨F, Submodule.subset_span hF⟩
      obtain ⟨f, S, φ, hf, hS, hRank, hSmooth, hSupport, hF⟩ := hF
      let f' : principalSeries ℝ (t + 1) (realPositionCharacter ds) := ⟨f, hf⟩
      let Φ := ofCompactSupport φ hSmooth S hS hSupport
      obtain ⟨hreg, hgrowth⟩ := hN f'
      obtain ⟨C, hC, hB⟩ := hM (additiveJacquetIntegral a f) hreg hgrowth Φ
      refine ⟨C, hC, fun g => ?_⟩
      change ‖J U g‖ ≤ C * realMatrixHeight g ^ M
      rw [hJ f' S hS hRank Φ hSupport U hF g]
      exact hB g
  | zero =>
      refine ⟨0, le_rfl, fun g => ?_⟩
      change ‖J 0 g‖ ≤ 0 * realMatrixHeight g ^ M
      simp only [map_zero, Pi.zero_apply, norm_zero, zero_mul, le_refl]
  | add F F' hF hF' ihF ihF' =>
      obtain ⟨C, hC, hBound⟩ := ihF
      obtain ⟨C', hC', hBound'⟩ := ihF'
      refine ⟨C + C', add_nonneg hC hC', fun g => ?_⟩
      change ‖J (⟨F, hF⟩ + ⟨F', hF'⟩) g‖ ≤ (C + C') * realMatrixHeight g ^ M
      simp only [map_add, Pi.add_apply]
      exact (norm_add_le _ _).trans ((add_le_add (hBound g) (hBound' g)).trans_eq (add_mul _ _ _).symm)
  | smul c F hF ih =>
      obtain ⟨C, hC, hBound⟩ := ih
      refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun g => ?_⟩
      change ‖J (c • ⟨F, hF⟩) g‖ ≤ (‖c‖ * C) * realMatrixHeight g ^ M
      simp only [map_smul, Pi.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hBound g) (norm_nonneg _)

end Langlands.Global.RankinSelbergGlobal.RealGodement
