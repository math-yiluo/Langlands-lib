import Langlands.Global.RankinSelberg.RealGodementTwoBlockRestriction
import Langlands.Global.RankinSelberg.UnfoldingDualGL

/-! # Lower rectangle insertion in the real Godement coefficient -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean Langlands.HarmonicAnalysis
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodementLowerRectangle

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant lowerBlockPair lowerBlockLocalization rankInclusion reindex)
open ArchimedeanLocal RealGodement RealJacquet
open RealGodementTwoBlockRestriction

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "XSpace" => fun r t => Matrix (Fin (r + 1 - (t + 1))) (Fin (t + 1)) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance lowerRectangleGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _

private theorem padGL_succ_eq_rankInclusion (n : ℕ) (g : G n) :
    padGL (Nat.le_succ n) g = rankInclusion 1 g := by
  ext i j
  have hcast (i : Fin n) : i.castSucc = i.castAdd 1 := rfl
  have hlast : Fin.last n = (0 : Fin 1).natAdd n := rfl
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    (simp [Unfolding.padGL_apply, rankInclusion, hcast, hlast, Fin.ext_iff]; try omega)

private theorem reindex_rankInclusion_one {m n : ℕ} (e : m = n) (g : G m) :
    reindex (finCongr (congrArg (· + 1) e)) (rankInclusion 1 g) =
      padGL (Nat.le_succ n) (reindex (finCongr e) g) := by
  subst n
  rw [padGL_succ_eq_rankInclusion]
  have h₁ : reindex (finCongr (congrArg (· + 1) (rfl : m = m))) (rankInclusion 1 g) = rankInclusion 1 g := by
    apply Units.ext
    ext i j
    rfl
  have h₂ : reindex (finCongr (rfl : m = m)) g = g := by
    apply Units.ext
    ext i j
    rfl
  rw [h₁, h₂]

/-- Insert a bottom-left rectangle between the smaller group and the final identity rows. -/
def lowerRectangle {r t : ℕ} (h : t < r) (X : XSpace r t) : G (r + 1) :=
  reindex (finCongr (Nat.add_sub_of_le (Nat.succ_le_succ h.le))) (lowerBlockPair 1 X 1)

theorem determinant_lowerRectangle {r t : ℕ} (h : t < r) (X : XSpace r t) :
    determinant (lowerRectangle h X) = 1 := by
  apply Units.ext
  let e := finCongr (Nat.add_sub_of_le (Nat.succ_le_succ h.le))
  change Matrix.det (Matrix.reindex e e (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) 0 X
      (1 : Matrix (Fin (r + 1 - (t + 1))) (Fin (r + 1 - (t + 1))) ℝ)))) = 1
  rw [Matrix.det_reindex_self, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, Matrix.det_one, mul_one]

/-- The rectangular input to the dual integral is a once-padded lower-block product. -/
theorem rectangularPoint_eq_pad_lowerRectangle {r t : ℕ} (h : t < r)
    (g : G (t + 1)) (X : XSpace r t) :
    ArchimedeanLocal.rectangularPoint (Nat.lt_succ_of_lt h) g X =
      padGL (Nat.le_succ (r + 1)) (padGL (Nat.succ_le_succ h.le) g * lowerRectangle h X) := by
  let e := Nat.add_sub_of_le (Nat.succ_le_succ h.le)
  change reindex (finCongr (congrArg (· + 1) e)) (rankInclusion 1 (lowerBlockPair g X 1)) = _
  rw [reindex_rankInclusion_one]
  congr 1
  have hLower := Unfolding.lowerBlockPair_mul_left g 1 X 1
  rw [mul_one] at hLower
  rw [hLower, map_mul]
  rfl

/-- The real Godement coefficient on the block argument of the dual local integral has the
fixed-rectangle right-tail formula and an absolutely integrable chart kernel. -/
def RealGodementLowerRectangleStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ν : AdditiveHaarMeasure ℝ) (μ₁ : Measure (G (t + 1)))
    (μ₂ : Measure (G (r + 1 - (t + 1)))) (κ : Measure (K (r + 1))),
    μ₁.IsHaarMeasure → μ₂.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
  ∀ D : RealQuotientMeasureData r, ∃ C : ℝ≥0, 0 < C ∧
    ∀ (ds : List RealBlock) (a : ℝˣ) (c : RealCharacterData)
      (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ, ℂ))
      (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ),
      (∀ A x, Φ (joinLastColumn A x) = F A * f x) →
    ∀ (U : G (r + 1) → ℂ), U ∈ realUniformWhittakerModel r ds (-a) →
      ∀ (g : G (t + 1)) (X : XSpace r t),
      let Fk := twoBlockRestrictionKernel (Nat.succ_pos t) (Nat.succ_lt_succ h) c a F f U g
        (lowerRectangle h X)
      let ρ := rightTailProductMeasure (r + 1) (t + 1) ν μ₁ μ₂ κ
      Integrable Fk ρ ∧
      realAdjacentGodementCoefficient D a Φ U c
          (ArchimedeanLocal.rectangularPoint (Nat.lt_succ_of_lt h) g X) =
        realAdjacentWeylSign r c * P g (1 / 2) * (C : ℂ) * ∫ p, Fk p ∂ρ

theorem realGodementLowerRectangle : RealGodementLowerRectangleStatement := by
  intro r t h ν μ₁ μ₂ κ hμ₁ hμ₂ hκ hκinv D
  obtain ⟨C, hC, hFormula⟩ := realGodementTwoBlockRestriction r (t + 1)
    (Nat.succ_pos t) (Nat.succ_lt_succ h) ν μ₁ μ₂ κ hμ₁ hμ₂ hκ hκinv D
  refine ⟨C, hC, ?_⟩
  intro ds a c Φ F f hΦ U hU g X
  obtain ⟨hi, he⟩ := hFormula ds a c Φ F f hΦ U hU g (lowerRectangle h X)
  refine ⟨hi, ?_⟩
  have hdet := determinant_lowerRectangle h X
  have hc : detCharacter c.character.toMonoidHom (lowerRectangle h X) = 1 := by
    unfold detCharacter
    rw [hdet, map_one, Units.val_one]
  have hp : P (lowerRectangle h X) (((r + 1 : ℕ) : ℂ) / 2) = 1 := by
    have hd : (lowerRectangle h X).val.det = 1 := congrArg Units.val hdet
    simp [ArchimedeanLocal.detPower, realNormalizedAbs, hd]
  rw [rectangularPoint_eq_pad_lowerRectangle h g X, he, hc, hp]
  ring

end Langlands.Global.RankinSelbergGlobal.RealGodementLowerRectangle
