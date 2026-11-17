import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Canonical affinization as a functor and its natural map -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.FlatPidAffinization

/-- Canonical affinization as a functor over an affine base. -/
abbrev affinizationFunctor (R : CommRingCat.{u}) : Over (Spec R) ⥤ Over (Spec R) :=
  algΓ R ⋙ algSpec R

@[simp] theorem affinizationFunctor_obj_hom (R : CommRingCat.{u}) (X : Over (Spec R)) :
    ((affinizationFunctor R).obj X).hom =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ X.hom.appTop) := rfl

@[simp] theorem affinizationFunctor_map_left (R : CommRingCat.{u})
    {X Y : Over (Spec R)} (f : X ⟶ Y) :
    ((affinizationFunctor R).map f).left = Spec.map f.left.appTop := rfl

/-- The canonical map from a scheme to its affinization, natural over the affine base. -/
def toAffinization (R : CommRingCat.{u}) : 𝟭 (Over (Spec R)) ⟶ affinizationFunctor R where
  app X := Over.homMk X.left.toSpecΓ (by
    change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ X.hom.appTop) = X.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id])
  naturality {X Y} f := by
    apply Over.OverMorphism.ext
    exact Scheme.toSpecΓ_naturality f.left

@[simp] theorem toAffinization_app_left (R : CommRingCat.{u}) (X : Over (Spec R)) :
    ((toAffinization R).app X).left = X.left.toSpecΓ := rfl

end Langlands.GroupScheme.FlatPidAffinization
