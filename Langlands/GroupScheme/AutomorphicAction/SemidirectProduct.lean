import Langlands.GroupScheme.AutomorphicAction
import Mathlib.GroupTheory.SemidirectProduct

/-! # The semidirect group scheme of an automorphic action -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {H G : GroupScheme B} (a : AutomorphicAction H G)

/-- The semidirect product of the actual groups of points of the action. -/
def semidirectPoints : (Over B)ᵒᵖ ⥤ GrpCat where
  obj T := GrpCat.of (SemidirectProduct (T.unop ⟶ G.X) (T.unop ⟶ H.X)
    (a.pointsAction T.unop))
  map f := GrpCat.ofHom (SemidirectProduct.map
    ((G.points.map f).hom) ((H.points.map f).hom) (by
      intro h
      apply MonoidHom.ext
      intro g
      exact a.naturality f.unop h g))
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply SemidirectProduct.ext
    · change 𝟙 T.unop ≫ x.left = x.left
      exact Category.id_comp _
    · change 𝟙 T.unop ≫ x.right = x.right
      exact Category.id_comp _
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply SemidirectProduct.ext
    · change (g.unop ≫ f.unop) ≫ x.left = g.unop ≫ f.unop ≫ x.left
      exact Category.assoc _ _ _
    · change (g.unop ≫ f.unop) ≫ x.right = g.unop ≫ f.unop ≫ x.right
      exact Category.assoc _ _ _

/-- The scheme product represents the semidirect point presheaf as a set functor. -/
def semidirectRepresentableBy :
    (a.semidirectPoints ⋙ forget GrpCat).RepresentableBy (G.X ⊗ H.X) where
  homEquiv :=
    { toFun := fun f => ⟨f ≫ fst G.X H.X, f ≫ snd G.X H.X⟩
      invFun := fun x => lift x.left x.right
      left_inv := by intro f; simp [← comp_lift]
      right_inv := by
        intro x
        apply SemidirectProduct.ext
        · exact lift_fst _ _
        · exact lift_snd _ _ }
  homEquiv_comp f g := by
    apply SemidirectProduct.ext <;> exact Category.assoc _ _ _

/-- The actual semidirect group scheme, with underlying scheme `G × H`. -/
def semidirectProduct : GroupScheme B :=
  letI := GrpObj.ofRepresentableBy (G.X ⊗ H.X)
    a.semidirectPoints a.semidirectRepresentableBy
  Grp.mk (G.X ⊗ H.X)

/-- Points of the semidirect group scheme have the standard semidirect group law. -/
def semidirectPointsIso : (a.semidirectProduct).points ≅ a.semidirectPoints :=
  yonedaGrpObjIsoOfRepresentableBy _ a.semidirectPoints a.semidirectRepresentableBy

/-- The canonical semidirect coordinates on every test scheme. -/
def semidirectPointsEquiv (T : Over B) :
    (T ⟶ a.semidirectProduct.X) ≃*
      SemidirectProduct (T ⟶ G.X) (T ⟶ H.X) (a.pointsAction T) :=
  (a.semidirectPointsIso.app (op T)).groupIsoToMulEquiv

@[simp] theorem semidirectPointsEquiv_left (T : Over B)
    (x : T ⟶ a.semidirectProduct.X) :
    (a.semidirectPointsEquiv T x).left = x ≫ fst G.X H.X := rfl

@[simp] theorem semidirectPointsEquiv_right (T : Over B)
    (x : T ⟶ a.semidirectProduct.X) :
    (a.semidirectPointsEquiv T x).right = x ≫ snd G.X H.X := rfl

/-- Semidirect coordinates commute with every test morphism. -/
theorem semidirectPointsEquiv_naturality {T V : Over B} (f : V ⟶ T)
    (x : T ⟶ a.semidirectProduct.X) :
    (a.semidirectPointsEquiv V (f ≫ x)).left =
      f ≫ (a.semidirectPointsEquiv T x).left ∧
    (a.semidirectPointsEquiv V (f ≫ x)).right =
      f ≫ (a.semidirectPointsEquiv T x).right :=
  ⟨Category.assoc _ _ _, Category.assoc _ _ _⟩

end Langlands.GroupScheme.AutomorphicAction
