import Langlands.Automorphic.FiniteOrderHeckeRealization
import Langlands.Automorphic.ConstantUnitaryForm
import Langlands.Automorphic.OperatorDeterminantUnitary

/-! # Positive forms on actual finite-order automorphic Hecke lines -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic.FiniteOrderHeckeRealization

open Langlands.Global ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance heckeUnitaryGroup1 : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeUnitaryGroup2 : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeUnitaryGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeUnitaryGroup4 : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance heckeUnitaryGroup5 : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeUnitaryGroup6 : AddCommGroup (realization F n χ hχ).Space :=
  Submodule.addCommGroup _
local instance heckeUnitaryGroup7 : AddCommGroup (ConstantFunctions.realization F n).Space :=
  Submodule.addCommGroup _

/-- A chosen positive form on the actual character line, using the actual multiplier. -/
def unitaryForm : (realization F n χ hχ).UnitaryForm :=
  (ConstantFunctions.unitaryForm F n).determinantTwist χ hχ

/-- The actual determinant multiplier is an isometry for these chosen forms. -/
theorem unitaryForm_inner_determinantTwistEquiv
    (f g : (ConstantFunctions.realization F n).Space) :
    (unitaryForm F n χ hχ).inner
      ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ f)
      ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ g) =
        (ConstantFunctions.unitaryForm F n).inner f g :=
  OperatorRealization.UnitaryForm.determinantTwist_inner_apply
    (ConstantFunctions.unitaryForm F n) χ hχ f g

@[simp]
theorem unitaryForm_inner_scalarEquiv (c d : ℂ) :
    (unitaryForm F n χ hχ).inner
      (scalarEquiv F n χ hχ c) (scalarEquiv F n χ hχ d) = d * star c := by
  change (unitaryForm F n χ hχ).inner
    ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ
      (ConstantFunctions.scalarEquiv F n c))
    ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ
      (ConstantFunctions.scalarEquiv F n d)) = _
  rw [unitaryForm_inner_determinantTwistEquiv,
    ConstantFunctions.unitaryForm_inner_scalarEquiv]

/-- The positive form is the usual scalar product in the actual line coordinates. -/
theorem unitaryForm_inner (f g : (realization F n χ hχ).Space) :
    (unitaryForm F n χ hχ).inner f g =
      inner ℂ ((scalarEquiv F n χ hχ).symm f) ((scalarEquiv F n χ hχ).symm g) := by
  obtain ⟨c, rfl⟩ := (scalarEquiv F n χ hχ).surjective f
  obtain ⟨d, rfl⟩ := (scalarEquiv F n χ hχ).surjective g
  have hcoords := congrArg₂ (fun u v : ℂ => inner ℂ u v)
    ((scalarEquiv F n χ hχ).symm_apply_apply c)
    ((scalarEquiv F n χ hχ).symm_apply_apply d)
  exact (unitaryForm_inner_scalarEquiv F n χ hχ c d).trans hcoords.symm

/-- Identity evaluation of the original represented functions gives the chosen form. -/
theorem unitaryForm_inner_evaluate (f g : (realization F n χ hχ).Space) :
    (unitaryForm F n χ hχ).inner f g =
      evaluate F n ((realization F n χ hχ).toContinuous g) 1 *
        star (evaluate F n ((realization F n χ hχ).toContinuous f) 1) := by
  rw [unitaryForm_inner, scalarEquiv_symm_apply, scalarEquiv_symm_apply]
  rfl

theorem realization_isUnitarizable : (realization F n χ hχ).IsUnitarizable :=
  ⟨unitaryForm F n χ hχ⟩

theorem realization_isoClass_isUnitarizable :
    (realization F n χ hχ).isoClass.IsUnitarizable :=
  ((realization F n χ hχ).isUnitarizable_isoClass).mpr
    (realization_isUnitarizable F n χ hχ)

theorem finiteRepresentation_isUnitarizable :
    Langlands.IsUnitarizable (realization F n χ hχ).finiteRepresentation :=
  (realization_isUnitarizable F n χ hχ).finite

theorem compactRepresentation_isUnitarizable :
    Langlands.IsUnitarizable (realization F n χ hχ).compactRepresentation :=
  (realization_isUnitarizable F n χ hχ).compact

theorem finiteImage_isUnitarizable :
    Langlands.IsUnitarizable (realization F n χ hχ).toFiniteRealization.representation :=
  (realization_isUnitarizable F n χ hχ).finiteImage

section RankOne

variable [CompactSpace (AdeleQuotient F)]

/-- The constructed rank-one cuspidal representative has the same positive form. -/
theorem cuspidal_isUnitarizable :
    (cuspidal F χ hχ).realization.IsUnitarizable :=
  realization_isUnitarizable F 1 χ hχ

/-- Its forgetful whole-operator class is unitarizable. -/
theorem cuspidalClass_isUnitarizable :
    (cuspidalClass F χ hχ).toOperatorClass.IsUnitarizable :=
  realization_isoClass_isUnitarizable F 1 χ hχ

end RankOne
end Langlands.Automorphic.FiniteOrderHeckeRealization
