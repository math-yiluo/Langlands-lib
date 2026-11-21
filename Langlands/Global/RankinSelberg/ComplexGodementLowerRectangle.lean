import Langlands.Global.RankinSelberg.ComplexGodementTwoBlockRestriction
import Langlands.Global.RankinSelberg.UnfoldingDualGL

/-! # Lower rectangle insertion in the complex Godement integral -/

noncomputable section

open MeasureTheory
open scoped NNReal Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementLowerRectangle

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant lowerBlockPair lowerBlockLocalization rankInclusion reindex)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementTwoBlockRestriction

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => unitaryCompact ℂ n
local notation "Rect" => fun r => Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ
local notation "XSpace" => fun r t => Matrix (Fin (r + 1 - (t + 1))) (Fin (t + 1)) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

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
  simp only [Langlands.RankinSelberg.reindex_finCongr_self]

/-- Insert a bottom-left rectangle between the smaller group and the final identity row. -/
def lowerRectangle {r t : ℕ} (h : t < r) (X : XSpace r t) : G (r + 1) :=
  reindex (finCongr (Nat.add_sub_of_le (Nat.succ_le_succ h.le))) (lowerBlockPair 1 X 1)

theorem determinant_lowerRectangle {r t : ℕ} (h : t < r) (X : XSpace r t) :
    determinant (lowerRectangle h X) = 1 := by
  apply Units.ext
  let e := finCongr (Nat.add_sub_of_le (Nat.succ_le_succ h.le))
  change Matrix.det (Matrix.reindex e e (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ) 0 X
      (1 : Matrix (Fin (r + 1 - (t + 1))) (Fin (r + 1 - (t + 1))) ℂ)))) = 1
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

/-- The continued complex Godement value on the block argument of the dual local integral
has the fixed-rectangle right-tail formula and an absolutely integrable chart kernel. -/
def ComplexGodementLowerRectangleStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ν : AdditiveHaarMeasure ℂ) (κ : Measure (K (r + 1))),
    κ.IsHaarMeasure → κ.IsInvInvariant → ∃ c : ℝ≥0, 0 < c ∧
    ∀ (ds : List ComplexCharacterData) (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ)
      (d : ComplexCharacterData) (Φ : 𝓢(Rect r, ℂ)) (W : complexWhittakerModel r ds (-a))
      (g : G (t + 1)) (X : XSpace r t) (s : ℂ),
      let F := twoBlockRestrictionKernel (Nat.succ_pos t) (Nat.succ_lt_succ h)
        μ d a Φ W.val g (lowerRectangle h X) s
      let ρ := rightTailProductMeasure (r + 1) (t + 1) ν κ
      Integrable F ρ ∧
      continuedValue (complexGeneralLinearHaar (r + 1)) μ d a Φ W.val
          (ArchimedeanLocal.rectangularPoint (Nat.lt_succ_of_lt h) g X) s =
        (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * P g (1 / 2) * (c : ℂ) * ∫ p, F p ∂ρ

theorem complexGodementLowerRectangle : ComplexGodementLowerRectangleStatement := by
  intro r t h ν κ hκ hκinv
  obtain ⟨c, hc, hFormula⟩ := complexGodementTwoBlockRestriction r (t + 1)
    (Nat.succ_pos t) (Nat.succ_lt_succ h) ν κ hκ hκinv
  refine ⟨c, hc, ?_⟩
  intro ds a μ d Φ W g X s
  obtain ⟨hi, he⟩ := hFormula ds a μ d Φ W g (lowerRectangle h X) s
  refine ⟨hi, ?_⟩
  rw [rectangularPoint_eq_pad_lowerRectangle h g X, he, determinant_lowerRectangle,
    map_one, mul_one]

end Langlands.Global.RankinSelbergGlobal.ComplexGodementLowerRectangle
