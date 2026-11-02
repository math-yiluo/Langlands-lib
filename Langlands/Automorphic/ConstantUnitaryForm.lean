import Langlands.Automorphic.ConstantFunctions
import Langlands.Automorphic.OperatorUnitaryForm
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # A positive invariant form on the actual constant automorphic line -/

noncomputable section
universe uF uG
set_option autoImplicit false

namespace Langlands.Automorphic.ConstantFunctions

open Langlands.Global ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance constantUnitaryGroup1 : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance constantUnitaryGroup2 : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance constantUnitaryGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance constantUnitaryGroup4 : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance constantUnitaryGroup5 : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance constantUnitaryGroup6 : AddCommGroup (realization F n).Space := Submodule.addCommGroup _

private def scalarPositiveForm (G : Type uG) [Monoid G] :
    Langlands.InvariantPositiveForm (Representation.trivial ℂ G ℂ) where
  toInnerProductCore := InnerProductSpace.toCore
  invariant _ _ _ := rfl

private def scalarFiniteEquiv :
    (Representation.trivial ℂ (FiniteAdelicGL F n) ℂ).Equiv
      (realization F n).finiteRepresentation :=
  Representation.Equiv.mk (scalarEquiv F n) (by
    intro d
    apply LinearMap.ext
    intro c
    exact (finiteRepresentation_scalarEquiv F n d c).symm)

private def finitePositiveForm :
    Langlands.InvariantPositiveForm (realization F n).finiteRepresentation :=
  (scalarPositiveForm (FiniteAdelicGL F n)).ofEquiv (scalarFiniteEquiv F n).symm

private theorem compact_fixes (k : standardInfiniteCompact F n)
    (f : (realization F n).Space) :
    (realization F n).compactRepresentation k f = f := by
  obtain ⟨c, rfl⟩ := (scalarEquiv F n).surjective f
  exact compactRepresentation_scalarEquiv F n k c

/-- The genuine real infinitesimal generator is zero on every actual constant vector. -/
theorem realGenerator_eq_zero (X : ArchimedeanGL.RealLieAlgebra F n)
    (f : (realization F n).Space) :
    (realization F n).envelopingAction
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) f = 0 := by
  obtain ⟨c, rfl⟩ := (scalarEquiv F n).surjective f
  have hscalar :
      ArchimedeanGL.augmentation F n
        (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) * c =
          (0 : ℂ) :=
    (congrArg (fun z : ℂ => z * c)
      (ArchimedeanGL.augmentation_envelopingGenerator F n
        (ArchimedeanGL.complexify F n X))).trans (zero_mul c)
  exact (envelopingAction_scalarEquiv F n _ c).trans
    ((congrArg (fun z : ℂ => scalarEquiv F n z) hscalar).trans
      (scalarEquiv F n).toLinearMap.map_zero)

/-- Pull back the usual positive scalar form to the actual constant function line.
Its finite and compact actions are trivial and its genuine real derivatives vanish. -/
def unitaryForm : (realization F n).UnitaryForm where
  finiteForm := finitePositiveForm F n
  compact_invariant k f g := by
    exact congrArg₂ (fun u v : (realization F n).Space =>
      (finitePositiveForm F n).inner u v)
        (compact_fixes F n k f) (compact_fixes F n k g)
  real_skew X f g := by
    have hzero :
        (finitePositiveForm F n).inner 0 g +
          (finitePositiveForm F n).inner f 0 = 0 := by
      change inner ℂ ((scalarEquiv F n).symm 0) ((scalarEquiv F n).symm g) +
        inner ℂ ((scalarEquiv F n).symm f) ((scalarEquiv F n).symm 0) = 0
      have hz := (scalarEquiv F n).symm.toLinearMap.map_zero
      exact (congrArg₂ (fun u v : ℂ =>
        inner ℂ u ((scalarEquiv F n).symm g) +
          inner ℂ ((scalarEquiv F n).symm f) v) hz hz).trans
            (by simp only [inner_zero_left, inner_zero_right, add_zero])
    exact (congrArg₂ (fun u v : (realization F n).Space =>
      (finitePositiveForm F n).inner u g + (finitePositiveForm F n).inner f v)
        (realGenerator_eq_zero F n X f) (realGenerator_eq_zero F n X g)).trans hzero

/-- The chosen form is the usual complex scalar product in the actual scalar coordinates. -/
@[simp] theorem unitaryForm_inner (f g : (realization F n).Space) :
    (unitaryForm F n).inner f g =
      inner ℂ ((scalarEquiv F n).symm f) ((scalarEquiv F n).symm g) := rfl

@[simp] theorem unitaryForm_inner_scalarEquiv (c d : ℂ) :
    (unitaryForm F n).inner (scalarEquiv F n c) (scalarEquiv F n d) =
      d * star c := by
  rw [unitaryForm_inner, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The positive form can be evaluated directly on the original represented functions. -/
theorem unitaryForm_inner_evaluate (f g : (realization F n).Space) :
    (unitaryForm F n).inner f g =
      evaluate F n ((realization F n).toContinuous g) 1 *
        star (evaluate F n ((realization F n).toContinuous f) 1) := by
  rw [unitaryForm_inner, scalarEquiv_symm_apply, scalarEquiv_symm_apply]
  rfl

theorem realization_isUnitarizable : (realization F n).IsUnitarizable :=
  ⟨unitaryForm F n⟩

theorem realization_isoClass_isUnitarizable :
    (realization F n).isoClass.IsUnitarizable :=
  ((realization F n).isUnitarizable_isoClass).mpr (realization_isUnitarizable F n)

theorem finiteImage_isUnitarizable :
    Langlands.IsUnitarizable (realization F n).toFiniteRealization.representation :=
  (realization_isUnitarizable F n).finiteImage

end Langlands.Automorphic.ConstantFunctions
