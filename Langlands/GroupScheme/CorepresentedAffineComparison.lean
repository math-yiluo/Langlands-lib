import Langlands.GroupScheme.CorepresentedPoints
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}}

/-- Relative global sections of an affine test scheme recover its original algebra. -/
def affineSectionsIso (S : CommAlgCat R) :
    ((algΓ R).obj ((algSpec R).obj (op S))).unop ≅ S :=
  (asIso ((algΓAlgSpecAdjunction R).counit.app (op S))).unop.symm

/-- The inverse algebra map is the actual relative adjunction counit, with opposites removed. -/
theorem affineSectionsIso_inv (S : CommAlgCat R) :
    (affineSectionsIso S).inv =
      ((algΓAlgSpecAdjunction R).counit.app (op S)).unop := rfl

/-- On rings, the counit map is the usual inverse global-sections/spectrum isomorphism. -/
theorem affineSectionsIso_inv_ringHom (S : CommAlgCat R) :
    (affineSectionsIso S).inv.hom.toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom := by
  rfl

/-- The forward map is the usual global-sections/spectrum isomorphism on rings. -/
theorem affineSectionsIso_hom_ringHom (S : CommAlgCat R) :
    (affineSectionsIso S).hom.hom.toRingHom =
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom := by
  ext z
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
  have h := ConcreteCategory.congr_hom (affineSectionsIso S).hom_inv_id z
  have h' := ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id z
  exact h.trans h'.symm

/-- The section comparison as an equivalence of algebras over the original base. -/
def affineSectionsAlgEquiv (S : CommAlgCat R) :
    ((algΓ R).obj ((algSpec R).obj (op S))).unop ≃ₐ[R] S :=
  CommAlgCat.algEquivOfIso (affineSectionsIso S)

/-- The inverse section comparison is natural in the test algebra. -/
theorem affineSectionsIso_inv_naturality {S T : CommAlgCat R} (f : S ⟶ T) :
    (affineSectionsIso S).inv ≫
        ((algΓ R).map ((algSpec R).map f.op)).unop =
      f ≫ (affineSectionsIso T).inv := by
  exact congrArg Quiver.Hom.unop ((algΓAlgSpecAdjunction R).counit.naturality f.op)

variable (F : CommAlgCat R ⥤ GrpCat.{u}) {B : CommAlgCat R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- On an affine test scheme the global-section coordinates are affine coordinates
transported through the inverse section isomorphism. -/
theorem pointsEquiv_eq_affinePointsEquiv (S : CommAlgCat R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme F e).X) :
    pointsEquiv F e ((algSpec R).obj (op S)) x =
      F.map (affineSectionsIso S).inv (affinePointsEquiv F e S x) := by
  rw [pointsEquiv_apply, affinePointsEquiv_apply, affineSectionsIso_inv]
  change (algSpec R).obj (op S) ⟶ (algSpec R).obj (op B) at x
  have h :
      (((algΓAlgSpecAdjunction R).homEquiv ((algSpec R).obj (op S)) (op B)).symm x) =
        (algΓAlgSpecAdjunction R).counit.app (op S) ≫
          algSpec.fullyFaithful.preimage x := by
    rw [Adjunction.homEquiv_counit]
    have h := (algΓAlgSpecAdjunction R).counit.naturality
      (algSpec.fullyFaithful.preimage x)
    simpa only [Functor.comp_map, Functor.id_map,
      algSpec.fullyFaithful.map_preimage] using h
  rw [h]
  exact e.homEquiv_comp _ _

/-- Transporting global-section coordinates back gives exactly the affine point comparison. -/
theorem map_affineSectionsIso_pointsEquiv (S : CommAlgCat R)
    (x : (algSpec R).obj (op S) ⟶ (groupScheme F e).X) :
    F.map (affineSectionsIso S).hom
        (pointsEquiv F e ((algSpec R).obj (op S)) x) =
      affinePointsEquiv F e S x := by
  rw [pointsEquiv_eq_affinePointsEquiv]
  change (F.map (affineSectionsIso S).inv ≫ F.map (affineSectionsIso S).hom)
    (affinePointsEquiv F e S x) = _
  rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
  rfl

end Langlands.GroupScheme.Corepresented
