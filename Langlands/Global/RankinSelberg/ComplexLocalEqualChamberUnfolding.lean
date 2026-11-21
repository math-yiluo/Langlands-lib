import Langlands.Global.RankinSelberg.ComplexLocalEqualPairedUnfolding
import Langlands.Global.RankinSelberg.ComplexLocalEqualProductConvergence
import Langlands.Global.RankinSelberg.ComplexLocalEqualProductSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalMatchedMatrixExpansion
import Langlands.Global.RankinSelberg.ComplexLocalAdjoiningShift

/-! # The original and dual equal-rank unfoldings in their respective chambers -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.GodementJacquet Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz)
open scoped Matrix.Norms.Elementwise SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (shiftedCharacter shiftedCharacter_exponent)
open ComplexCharacterChange (model_unipotent_mul)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "ud" => ArchimedeanLocal.dualFunction m
local notation "wd" => ArchimedeanLocal.dualFunction n

private theorem equal_unfolds_in_chamber
    (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (a : ℂˣ) (d : ComplexCharacterData) {ds es : List ComplexCharacterData}
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (Φ : EntrySchwartz m n) (φ : 𝓢(Row, ℂ)) (c : ℝ≥0)
    (hrec : ∀ (η : ℂˣ →* ℂˣ) (g : G),
      complexEqualUnipotentRecursion D D₁ η a Φ U.val g =
        (c : ℂ) * complexJacquetRecursion a D₁ Φ U.val η g) :
    ∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
      let η := (shiftedCharacter d z).character.toMonoidHom
      (c : ℂ) * complexEqualIntegral D (complexJacquetRecursion a D₁ Φ U.val η) V.val φ s =
        complexEqualUnfoldedIntegral D.groupHaar D₁ η (complexSquareProductTest Φ φ) U.val V.val s := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let Ψ := complexMatrixEntryToOperator (complexSquareProductSchwartz Φ φ)
  have hΨ : (Ψ : Mat → ℂ) = complexSquareProductTest Φ φ :=
    funext (complexSquareProductSchwartz_apply Φ φ)
  obtain ⟨T, σ, hI⟩ := complexLocalEqualProductConvergence D₁ D.groupHaar a ds es U V
  refine ⟨T - d.exponent.re, σ, ?_⟩
  intro z s hz hs η
  let d' := shiftedCharacter d z
  have hd' : T ≤ d'.exponent.re := by
    dsimp only [d']
    rw [shiftedCharacter_exponent, Complex.add_re]
    linarith
  have hCont := continuous_complexEqualUnfoldedKernel U V d' Ψ s
  have hInt := hI d' hd' Ψ s hs
  rw [hΨ] at hCont hInt
  let R := complexEqualUnipotentRecursion D D₁ η a Φ U.val
  calc
    _ = complexEqualIntegral D R V.val φ s :=
      complexEqualIntegral_scale_left_of_eq D c _ R V.val φ s (fun g => (hrec η g).symm)
    _ = _ := complexLocalEqualUnfoldingFubini D D₁ η a Φ φ R V.val U.val
      (fun _ => rfl) (model_unipotent_mul V.2) s hCont hInt

private theorem inverseShift_at_neg_one (d : ComplexCharacterData) (z : ℂ) :
    ((shiftedCharacter d.inv z).character (-1) : ℂ) = (d.character (-1) : ℂ) := by
  have h : ((shiftedCharacter d.inv z).character (-1) : ℂ) = (d.inv.character (-1) : ℂ) := by
    rw [(shiftedCharacter d.inv z).character_eq, d.inv.character_eq]
    simp [shiftedCharacter, Langlands.Archimedean.characterOfParams_weight]
  rw [h]
  have hu : d.inv.character (-1) = d.character (-1) := by
    change (d.character (-1))⁻¹ = _
    rw [← map_inv]
    simp
  exact congrArg Units.val hu

/-- The scalar is common to the two separate positive adjoining-exponent
chambers, with the dual chamber expressed through the opposite recursion. -/
def ComplexLocalEqualChamberUnfoldingStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ),
  ∃ c : ℝ≥0, 0 < c ∧
  ∀ (d : ComplexCharacterData) (ds es : List ComplexCharacterData), ds.length = m → es.length = n →
  ∀ (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (Φ Φd : EntrySchwartz m n) (φ φd : 𝓢(Row, ℂ)),
    (Φd : Rect → ℂ) = complexRectangularFourier (-a) Φ →
    (φd : Row → ℂ) = complexFourierTransform a φ →
    let b := (d.character (-1) : ℂ) ^ m
    let Ψ := complexSquareProductTest Φ φ
    (∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
      let η := (shiftedCharacter d z).character.toMonoidHom
      (c : ℂ) * complexEqualIntegral D (complexJacquetRecursion a D₁ Φ U.val η) V.val φ s =
        complexEqualUnfoldedIntegral D.groupHaar D₁ η Ψ U.val V.val s) ∧
    (∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
      let η := (shiftedCharacter d.inv z).character.toMonoidHom
      ((c : ℂ) * b) * complexEqualIntegral D
        (complexJacquetRecursion (-a) D₁ Φd (ud U.val) η) (wd V.val) φd s =
        complexCentralSign ds * complexEqualUnfoldedIntegral D.groupHaar D₁ η
          (complexMatrixFourier a Ψ) (ud U.val) (wd V.val) s)

theorem complexLocalEqualChamberUnfolding : ComplexLocalEqualChamberUnfoldingStatement (r := r) := by
  intro D D₁ a
  obtain ⟨c, hc, hrec⟩ := complexLocalEqualRecursionComparison (r := r) D D₁ a
  refine ⟨c, hc, ?_⟩
  intro d ds es hds hes U V Φ Φd φ φd hΦd hφd b Ψ
  refine ⟨equal_unfolds_in_chamber D D₁ a d U V Φ φ c (hrec a rfl · Φ U.val), ?_⟩
  let Ud : complexWhittakerModel r (dualData ds) (-a) := ⟨_, dualFunction_mem hds U.2⟩
  let Vd : complexWhittakerModel (r + 1) (dualData es) (-(-a)) := ⟨_, dualFunction_mem hes V.2⟩
  obtain ⟨τ, σ, hI⟩ := equal_unfolds_in_chamber D D₁ (-a) d.inv Ud Vd Φd φd c
    (hrec (-a) (complexSelfDualMeasure_neg_scale a) · Φd Ud.val)
  refine ⟨τ, σ, ?_⟩
  intro z s hz hs η
  have hb : (η (-1) : ℂ) ^ m = b :=
    congrArg (fun y : ℂ => y ^ m) (inverseShift_at_neg_one d z)
  have he := hI z s hz hs
  change (c : ℂ) * complexEqualIntegral D (complexJacquetRecursion (-a) D₁ Φd Ud.val η)
    Vd.val φd s = _ at he
  calc
    _ = b * complexEqualUnfoldedIntegral D.groupHaar D₁ η (complexSquareProductTest Φd φd)
        Ud.val Vd.val s := by
      rw [mul_comm (c : ℂ) b, mul_assoc, he]
    _ = _ := by
      rw [← hb, hΦd, hφd]
      exact complexEqualUnfoldedSign_of_mem D D₁ η a ds es hds hes U V Φ φ s

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
