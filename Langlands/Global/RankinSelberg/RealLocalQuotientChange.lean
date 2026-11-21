import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.Global.RankinSelberg.UnipotentConjugationModulus
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization

/-! # Transport of compatible real quotient measure data by normalizing matrices -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCharacterChange

open ArchimedeanLocal Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open UnipotentConjugationModulus (conjugation conjugation_apply)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ

/-- All invertible real diagonal matrices normalize the quotient subgroup. -/
theorem conjugation_diagonal_mem_iff (d : Fin (r + 1) → ℝˣ) (g : G) :
    conjugation (GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) d) g ∈ N ↔ g ∈ N := by
  open Langlands.Whittaker.UpperUnipotentCharacter in
  have h (d' : Fin (r + 1) → ℝˣ) (x : G) (hx : x ∈ N) :
      GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) d' * x *
        (GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) d')⁻¹ ∈ N := by
    have hd : diagonalUnit d' = GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) d' := Units.ext rfl
    rw [← hd]
    exact diagonalUnit_conj_mem d' hx
  let t := GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) d
  rw [conjugation_apply]
  refine ⟨fun hx => ?_, h d g⟩
  have hi := h d⁻¹ (t * g * t⁻¹) hx
  rw [map_inv, inv_inv] at hi
  change t⁻¹ * (t * g * t⁻¹) * t ∈ N at hi
  rwa [show t⁻¹ * (t * g * t⁻¹) * t = g by group] at hi

variable (t : Langlands.GeneralLinear (r + 1) ℝ)
  (ht : ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
    conjugation t g ∈ GeneralLinear.upperUnipotent (r + 1) ℝ ↔
      g ∈ GeneralLinear.upperUnipotent (r + 1) ℝ)

private def conjugationQuotient : Q ≃ₜ Q :=
  quotientAutomorphism N (conjugation t) ht

/-- Simultaneously transport the group, unipotent and quotient measures by conjugation
by a normalizing matrix, such as the character-changing diagonal. -/
def changeQuotientMeasure (D : RealQuotientMeasureData r) : RealQuotientMeasureData r := by
  let e := conjugation t
  let eN := subgroupAutomorphism N e ht
  let eQ := conjugationQuotient t ht
  letI := D.groupHaar_isHaar
  letI := D.unipotentHaar_isHaar
  letI := D.unipotentHaar_rightInvariant
  exact
    { groupHaar := Measure.map e D.groupHaar
      groupHaar_isHaar := e.isHaarMeasure_map D.groupHaar
      unipotentHaar := Measure.map eN D.unipotentHaar
      unipotentHaar_isHaar := eN.isHaarMeasure_map D.unipotentHaar
      unipotentHaar_rightInvariant := isMulRightInvariant_map eN D.unipotentHaar
      measure := Measure.map eQ D.measure
      compatible := isCompatible_map_equiv e N N eN (fun _ => rfl) eQ (fun _ => rfl)
        D.groupHaar D.unipotentHaar D.measure D.compatible }

/-- On quotient representatives the shift is `g ↦ t g z`, with `t` normalizing the
quotient subgroup and `z` arbitrary. -/
def shiftQuotient (z : G) : Q ≃ₜ Q :=
  (conjugationQuotient t ht).trans (rightTranslate N (t * z))

theorem shiftQuotient_mk (z g : G) :
    shiftQuotient t ht z (Quotient.mk _ g) = Quotient.mk _ (t * g * z) := by
  change Quotient.mk _ (t * g * t⁻¹ * (t * z)) = _
  congr 1
  group

/-- The shift transports the original quotient measure to the new compatible measure,
independently of the final right shift. -/
theorem measurePreserving_shiftQuotient (D : RealQuotientMeasureData r) (z : G) :
    MeasurePreserving (shiftQuotient t ht z) D.measure (changeQuotientMeasure t ht D).measure := by
  have h : MeasurePreserving (conjugationQuotient t ht) D.measure
      (changeQuotientMeasure t ht D).measure :=
    ⟨(conjugationQuotient t ht).continuous.measurable, rfl⟩
  let := (changeQuotientMeasure t ht D).unipotentHaar_rightInvariant
  exact ((changeQuotientMeasure t ht D).compatible.right_invariant _).comp h

end Langlands.Global.RankinSelbergGlobal.RealCharacterChange
