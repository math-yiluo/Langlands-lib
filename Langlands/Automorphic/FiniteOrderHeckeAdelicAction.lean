import Langlands.Automorphic.FiniteOrderHeckeUnitaryForm
import Langlands.Representation.Unitary.ScalarAction

/-! # Full adelic actions on actual finite-order automorphic Hecke lines -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic.FiniteOrderHeckeRealization

open Langlands.Global ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance heckeAdelicActionGroup1 : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeAdelicActionGroup2 : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeAdelicActionGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeAdelicActionGroup4 : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance heckeAdelicActionGroup5 : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance heckeAdelicActionGroup6 : AddCommGroup (realization F n χ hχ).Space :=
  Submodule.addCommGroup _

/-- The actual determinant character acts on the original function line. -/
def adelicRepresentation :
    Representation ℂ (AdelicGL F n) (realization F n χ hχ).Space :=
  Langlands.twist (χ.adelicDeterminant n).toMonoidHom
    (Representation.trivial ℂ (AdelicGL F n) (realization F n χ hχ).Space)

@[simp]
theorem adelicRepresentation_apply (g : AdelicGL F n)
    (f : (realization F n χ hχ).Space) :
    adelicRepresentation F n χ hχ g f = (χ.adelicDeterminant n g : ℂ) • f := rfl

theorem adelicRepresentation_scalarEquiv (g : AdelicGL F n) (c : ℂ) :
    adelicRepresentation F n χ hχ g (scalarEquiv F n χ hχ c) =
      scalarEquiv F n χ hχ ((χ.adelicDeterminant n g : ℂ) * c) :=
  ((scalarEquiv F n χ hχ).map_smul (χ.adelicDeterminant n g : ℂ) c).symm

/-- The full action is positive right translation on the actual adelic functions. -/
theorem evaluate_adelicRepresentation (g x : AdelicGL F n)
    (f : (realization F n χ hχ).Space) :
    evaluate F n ((realization F n χ hχ).toContinuous
      (adelicRepresentation F n χ hχ g f)) x =
        evaluate F n ((realization F n χ hχ).toContinuous f) (x * g) :=
  Langlands.scalarEquiv_right_translation (scalarEquiv F n χ hχ)
    (fun v => evaluate F n ((realization F n χ hχ).toContinuous v))
    (χ.adelicDeterminant n).toMonoidHom (evaluate_scalarEquiv F n χ hχ) g x f

/-- Restriction is the already constructed finite translation on the same carrier. -/
theorem adelicRepresentation_ofFinite (d : FiniteAdelicGL F n)
    (f : (realization F n χ hχ).Space) :
    adelicRepresentation F n χ hχ (AdelicGL.ofFinite F n d) f =
      (realization F n χ hχ).finiteRepresentation d f :=
  (Langlands.operator_eq_smul_of_scalarEquiv (scalarEquiv F n χ hχ)
    ((realization F n χ hχ).finiteRepresentation d)
    (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ)
    (finiteRepresentation_scalarEquiv F n χ hχ d) f).symm

/-- The standard compact restriction is the original compact translation. -/
theorem adelicRepresentation_ofCompact (k : standardInfiniteCompact F n)
    (f : (realization F n χ hχ).Space) :
    adelicRepresentation F n χ hχ (AdelicGL.ofInfinite F n k.val) f =
      (realization F n χ hχ).compactRepresentation k f :=
  (Langlands.operator_eq_smul_of_scalarEquiv (scalarEquiv F n χ hχ)
    ((realization F n χ hχ).compactRepresentation k)
    (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ)
    (compactRepresentation_scalarEquiv F n χ hχ k) f).symm

include hχ in
theorem adelicDeterminant_norm (g : AdelicGL F n) :
    ‖(χ.adelicDeterminant n g : ℂ)‖ = 1 :=
  hχ.isUnitary (ideleClassMap F (AdelicGL.determinant F n g))

/-- A full-group invariant form with exactly the chosen finite positive core. -/
def adelicUnitaryForm :
    Langlands.InvariantPositiveForm (adelicRepresentation F n χ hχ) :=
  (unitaryForm F n χ hχ).finiteForm.scalarActionForm
    (χ.adelicDeterminant n).toMonoidHom (adelicDeterminant_norm F n χ hχ)

@[simp]
theorem adelicUnitaryForm_inner (f g : (realization F n χ hχ).Space) :
    (adelicUnitaryForm F n χ hχ).inner f g = (unitaryForm F n χ hχ).inner f g := rfl

/-- The actual completed representation, jointly continuous on the same Hilbert
space as the finite and compact actions. -/
def completedAdelicAction :
    C(AdelicGL F n × (unitaryForm F n χ hχ).finiteForm.HilbertCompletion,
      (unitaryForm F n χ hχ).finiteForm.HilbertCompletion) :=
  (unitaryForm F n χ hχ).finiteForm.scalarContinuousAction
    (χ.adelicDeterminant n).toMonoidHom (adelicDeterminant_norm F n χ hχ)
    (Units.continuous_val.comp (χ.adelicDeterminant n).continuous)

@[simp]
theorem completedAdelicAction_apply (g : AdelicGL F n)
    (x : (unitaryForm F n χ hχ).finiteForm.HilbertCompletion) :
    completedAdelicAction F n χ hχ (g, x) = (χ.adelicDeterminant n g : ℂ) • x :=
  (unitaryForm F n χ hχ).finiteForm.scalarContinuousAction_apply
    (χ.adelicDeterminant n).toMonoidHom (adelicDeterminant_norm F n χ hχ)
    (Units.continuous_val.comp (χ.adelicDeterminant n).continuous) g x

theorem completedAdelicAction_toHilbert (g : AdelicGL F n)
    (f : (realization F n χ hχ).Space) :
    completedAdelicAction F n χ hχ (g, (unitaryForm F n χ hχ).finiteForm.toHilbert f) =
      (unitaryForm F n χ hχ).finiteForm.toHilbert (adelicRepresentation F n χ hχ g f) :=
  (adelicUnitaryForm F n χ hχ).completedRepresentation_toHilbert g f

@[simp]
theorem completedAdelicAction_ofFinite (d : FiniteAdelicGL F n)
    (x : (unitaryForm F n χ hχ).finiteForm.HilbertCompletion) :
    completedAdelicAction F n χ hχ (AdelicGL.ofFinite F n d, x) =
      (unitaryForm F n χ hχ).finiteForm.completedOperator d x :=
  (completedAdelicAction_apply F n χ hχ (AdelicGL.ofFinite F n d) x).trans
    (((unitaryForm F n χ hχ).finiteForm.completedOperator_eq_smul d
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ)
      (fun f => (adelicRepresentation_ofFinite F n χ hχ d f).symm) x).symm)

@[simp]
theorem completedAdelicAction_ofCompact (k : standardInfiniteCompact F n)
    (x : (unitaryForm F n χ hχ).finiteForm.HilbertCompletion) :
    completedAdelicAction F n χ hχ (AdelicGL.ofInfinite F n k.val, x) =
      (unitaryForm F n χ hχ).compactForm.completedOperator k x :=
  (completedAdelicAction_apply F n χ hχ (AdelicGL.ofInfinite F n k.val) x).trans
    (((unitaryForm F n χ hχ).compactForm.completedOperator_eq_smul k
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ)
      (fun f => (adelicRepresentation_ofCompact F n χ hχ k f).symm) x).symm)

end Langlands.Automorphic.FiniteOrderHeckeRealization
