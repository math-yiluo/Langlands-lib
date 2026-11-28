import Langlands.Geometry.Analytic.GroundFieldExtensionSemilinearAction
import Mathlib.CategoryTheory.Action.Basic

/-! # Equivariant scalar extension on analytic morphisms -/

noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

universe u v

namespace Langlands.Analytic.SpaceOverField

open CompleteUltrametricField

private abbrev fibreInclusion (K : CompleteUltrametricField.{u}) :
    K.CompatibleAnalyticCategory.{u, v} ⥤ SpaceOverField.{u, v} :=
  Pseudofunctor.CoGrothendieck.ι scalarExtensionPseudofunctor (op K)

variable {K L : CompleteUltrametricField.{u}} (e : K ⟶ L)
variable {Y X : K.CompatibleAnalyticCategory.{u, v}}

/-- Scalar extension followed by the inclusion of the target analytic fibre. -/
def scalarExtendedFunctor : K.CompatibleAnalyticCategory.{u, v} ⥤ SpaceOverField.{u, v} :=
  localizedExtend e ⋙ fibreInclusion L

/-- The Cartesian projections from scalar extension are natural for maps over
 the original field. -/
@[reassoc]
theorem scalarExtendedFunctor_projection (f : Y ⟶ X) :
    (scalarExtendedFunctor e).map f ≫ scalarExtensionArrow (withField K X) e =
      scalarExtensionArrow (withField K Y) e ≫ (fibreInclusion K).map f := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _
    ((Category.id_comp e.op).trans (Category.comp_id e.op).symm) ?_
  let E := localizedExtend.{u, v} e
  let h₁ := (localizedExtendComp (𝟙 K) e).app X
  let h₂ := (localizedExtendComp e (𝟙 L)).app X
  let uK := (localizedExtendId K).app X
  let uL := (localizedExtendId L).app (E.obj X)
  have leftUnit : h₁ ≪≫ E.mapIso uK = eqToIso
      (congrArg (fun d => (localizedExtend.{u, v} d).obj X) (Category.id_comp e)) :=
    Iso.ext (localizedExtend_id_left e X)
  have rightUnit : h₂ ≪≫ uL = eqToIso
      (congrArg (fun d => (localizedExtend.{u, v} d).obj X) (Category.comp_id e)) :=
    Iso.ext (localizedExtend_id_right e X)
  have leftUnit_inv : E.map uK.inv ≫ h₁.inv = eqToHom
      (congrArg (fun d => (localizedExtend.{u, v} d).obj X) (Category.id_comp e)).symm :=
    congrArg Iso.inv leftUnit
  have rightUnit_inv : uL.inv ≫ h₂.inv = eqToHom
      (congrArg (fun d => (localizedExtend.{u, v} d).obj X) (Category.comp_id e)).symm :=
    congrArg Iso.inv rightUnit
  change (E.map f ≫ uL.inv) ≫ (localizedExtend (𝟙 L)).map (𝟙 (E.obj X)) ≫ h₂.inv =
    (𝟙 (E.obj Y) ≫ E.map (f ≫ uK.inv) ≫ h₁.inv) ≫ eqToHom _
  simp only [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp, Category.id_comp,
    Category.assoc]
  rw [rightUnit_inv, reassoc_of% leftUnit_inv, eqToHom_trans]

/-- An extended map commutes with the semilinear coefficient lifts. -/
theorem scalarExtendedFunctor_coefficientLift (f : Y ⟶ X) (σ : CoefficientAutomorphisms e) :
    coefficientLift e Y σ ≫ (scalarExtendedFunctor e).map f =
      (scalarExtendedFunctor e).map f ≫ coefficientLift e X σ := by
  let d := (coefficientFieldMap σ⁻¹).op
  let p := scalarExtensionArrow (withField K X) e
  let : fieldProjection.IsStronglyCartesian e.op p :=
    scalarExtensionArrow_isStronglyCartesian (withField K X) e
  have h (Z : K.CompatibleAnalyticCategory.{u, v}) :
      fieldProjection.IsHomLift d (coefficientLift e Z σ) := by
    have hfield : fieldProjection.map (coefficientLift e Z σ) = d :=
      congrArg Quiver.Hom.op (fieldMap_coefficientLift e Z σ)
    exact hfield ▸ IsHomLift.map fieldProjection _
  let : fieldProjection.IsHomLift d (coefficientLift e Y σ) := h Y
  let : fieldProjection.IsHomLift d (coefficientLift e X σ) := h X
  let : fieldProjection.IsHomLift (𝟙 (op L)) ((scalarExtendedFunctor e).map f) :=
    IsHomLift.map fieldProjection ((scalarExtendedFunctor e).map f)
  apply IsStronglyCartesian.ext fieldProjection e.op p d
  change (coefficientLift e Y σ ≫ (scalarExtendedFunctor e).map f) ≫
      scalarExtensionArrow (withField K X) e =
    ((scalarExtendedFunctor e).map f ≫ coefficientLift e X σ) ≫
      scalarExtensionArrow (withField K X) e
  simp only [Category.assoc, scalarExtendedFunctor_projection, coefficientLift_comp_projection,
    reassoc_of% coefficientLift_comp_projection]

/-- Scalar extension equipped with the action by isometric coefficient
automorphisms that fix the original ground field. -/
def coefficientEquivariantScalarExtension :
    K.CompatibleAnalyticCategory.{u, v} ⥤
      Action SpaceOverField.{u, v} (CoefficientAutomorphisms e) where
  obj X := ⟨scalarExtendedSpace e X, Aut.toEnd.comp (coefficientAnalyticAction e X)⟩
  map f := ⟨(scalarExtendedFunctor e).map f, scalarExtendedFunctor_coefficientLift e f⟩
  map_id X := Action.Hom.ext ((scalarExtendedFunctor e).map_id X)
  map_comp f g := Action.Hom.ext ((scalarExtendedFunctor e).map_comp f g)

end Langlands.Analytic.SpaceOverField
