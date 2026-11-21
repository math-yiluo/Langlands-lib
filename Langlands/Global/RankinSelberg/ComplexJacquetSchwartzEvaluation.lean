import Langlands.Global.RankinSelberg.ComplexGodementSchwartzOpenCell
import Langlands.Global.RankinSelberg.ComplexJacquetEvaluation

/-! # Canonical Jacquet evaluation of Schwartz Godement sections in a strict chamber -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (characterOfParams_exponent)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz operatorToEntry operatorToEntry_apply)
open ComplexCompactProfileFamily (characterList)
open ComplexGodement (godementSection addedCharacter retainedCharacters smallerWeights smallerExponents
  characterList_cons)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementGeneratorFamily (isStrictlyDominant_characterList)
open ComplexGodementSchwartzOpenCell (complexGodementSchwartzOpenCell)
open ComplexJacquetChamberHolomorphic (chamber)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "P" => Fin (r + 1 + 1) → ℂ
local notation "L" => Fin (r + 1 + 1) → ℤ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Small[" l "," p "]" =>
  Automorphic.complexStandardKFinite (r + 1) (retainedCharacters l p)
local notation "Large[" l "," p "]" =>
  Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p)

private theorem smaller_in_chamber {p : P} (hp : p ∈ chamber (r + 1)) :
    smallerExponents p ∈ chamber r := by
  intro i
  have h := hp i.succ
  change (p i.succ.succ).re < (p i.succ.castSucc).re at h
  rw [show i.succ.castSucc = i.castSucc.succ from Fin.ext rfl] at h
  exact h

/-- In the strict chamber with a sufficiently large adjoining exponent, the canonical
Jacquet value of a Schwartz Godement section is the continued Godement value at zero shift
of the actual adjoining character, applied to the smaller canonical Jacquet value. -/
def ComplexJacquetSchwartzEvaluationStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (l : L) (q : Fin (r + 1) → ℂ),
    ∃ M : ℕ, ∀ p : P, smallerExponents p = q → p ∈ chamber (r + 1) →
    ((r + 1 : ℕ) : ℝ) + M ≤ (p 0 + ((((r + 1 : ℕ) : ℂ) + 1) / 2)).re →
    ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (Φ : OperatorSchwartz (r + 1) (r + 1 + 1))
      (f : Small[l, p]) (F : Large[l, p]),
    F.val = godementSection ν (addedCharacter l p) Φ f.val →
    continuedJacquet μ a l p F =
      fun g : G => continuedValue ν μ (addedCharacter l p) a (operatorToEntry Φ)
        (continuedJacquet μ a (smallerWeights l) (smallerExponents p) f) g 0

set_option maxHeartbeats 700000 in
theorem complexJacquetSchwartzEvaluation : ComplexJacquetSchwartzEvaluationStatement (r := r) := by
  intro ν hν hνr l q
  obtain ⟨M, hM⟩ := complexGodementSchwartzOpenCell (r := r) ν
    (characterList (smallerWeights l) q) List.length_ofFn
  refine ⟨M, fun p hq hp hd μ a Φ f F hF => ?_⟩
  subst q
  have hstrict := isStrictlyDominant_characterList l hp
  rw [characterList_cons] at hstrict
  have hd' : ((r + 1 : ℕ) : ℝ) + M ≤
      ((addedCharacter l p).exponent + ((((r + 1 : ℕ) : ℂ) + 1) / 2)).re := by
    simpa only [addedCharacter, characterOfParams_exponent] using hd
  rw [continuedJacquet_chamber μ a l p hp F, hF,
    continuedJacquet_chamber μ a (smallerWeights l) (smallerExponents p) (smaller_in_chamber hp) f]
  funext g
  have h := (hM (addedCharacter l p) hstrict hd' μ a Φ f.val f.2.1 g).2
  rw [h]
  have hX : (rightTest g (operatorToEntry Φ) : Rect → ℂ) = fun X => Φ (X * g.val) := by
    funext X
    exact (rightTest_apply g (operatorToEntry Φ) X).trans (operatorToEntry_apply Φ _)
  unfold continuedValue
  simp only [hX, ArchimedeanLocal.detPower, zero_mul, Complex.exp_zero, mul_one, add_zero]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
