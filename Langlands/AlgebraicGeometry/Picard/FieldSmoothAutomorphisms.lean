import Langlands.AlgebraicGeometry.Picard.SmoothUnitBaseChange
import Langlands.AlgebraicGeometry.Units.FieldGlobalFunctions
import Langlands.AlgebraicGeometry.Units.FiniteAlgebraRepresentability
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Smooth actual relative automorphisms of a proper field scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- The determinant-open unit scheme of the actual finite global-functions
algebra of a proper field scheme. -/
def fieldUnitScheme : Over (Spec (CommRingCat.of k)) := by
  letI := GlobalFunctionsAlgebra.algebra f
  letI := FieldGlobalFunctions.finite_algebra f
  exact FiniteAlgebraUnits.candidate (Module.finBasis k Γ(X, ⊤))

/-- The full natural representation of relative global units by this scheme,
using the actual canonical map to the global-functions spectrum. -/
def fieldUnitSchemeIso :
    (AlgebraicSpace.schemeYoneda _).obj (fieldUnitScheme f) ≅
      RelativeGlobalUnits.presheaf f := by
  letI := GlobalFunctionsAlgebra.algebra f
  letI := FieldGlobalFunctions.finite_algebra f
  let b := Module.finBasis k Γ(X, ⊤)
  letI : IsIso (FiniteAlgebraUnits.candidateMap b) :=
    (FiniteAlgebraUnits.representability k Γ(X, ⊤) _ b).1
  let e := asIso (FiniteAlgebraUnits.candidateMap b)
  exact e ≪≫ (FieldGlobalUnits.finiteAlgebraPresheafIso f).symm

/-- The actual unit scheme over the field is smooth. -/
lemma fieldUnitScheme_smooth : Smooth (fieldUnitScheme f).hom := by
  let := GlobalFunctionsAlgebra.algebra f
  let := FieldGlobalFunctions.finite_algebra f
  exact (FiniteAlgebraUnits.representability k Γ(X, ⊤) _
    (Module.finBasis k Γ(X, ⊤))).2

/-- Actual relative global units admit smooth scheme representatives after
every scheme base change. -/
lemma field_hasSmoothUnitSchemes : HasSmoothUnitSchemes f :=
  hasSmoothUnitSchemes_of_unitScheme f (fieldUnitScheme f)
    (fieldUnitSchemeIso f) (fieldUnitScheme_smooth f)

/-- Every actual line bundle on every relative scheme test has a smooth
scheme representing its full actual relative automorphism presheaf. -/
lemma field_hasSmoothRelativeAutomorphismSchemes :
    HasSmoothRelativeAutomorphismSchemes f :=
  (field_hasSmoothUnitSchemes f).hasSmoothRelativeAutomorphismSchemes f

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
