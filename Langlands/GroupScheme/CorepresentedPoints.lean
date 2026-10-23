import Langlands.GroupScheme.Corepresented

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} (F : CommAlgCat R ⥤ GrpCat.{u}) {B : CommAlgCat R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

local instance : GrpObj (cogroup F e).X := (cogroup F e).grp

/-- The relative Spec adjunction respects multiplication of points. -/
def adjunctionPointsEquiv (T : Over (Spec R)) :
    ((algΓ R).obj T ⟶ (cogroup F e).X) ≃* (T ⟶ (groupScheme F e).X) := by
  letI := (cogroup F e).grp
  exact
    { (algΓAlgSpecAdjunction R).homEquiv T (cogroup F e).X with
      map_mul' := fun f g => by
        change (algΓAlgSpecAdjunction R).homEquiv T (op B) (f * g) =
          (algΓAlgSpecAdjunction R).homEquiv T (op B) f *
            (algΓAlgSpecAdjunction R).homEquiv T (op B) g
        simp only [Adjunction.homEquiv_unit, Functor.map_mul, MonObj.comp_mul] }

/-- Points on any test scheme are the original functor on its relative global sections. -/
def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme F e).X) ≃* F.obj ((algΓ R).obj T).unop :=
  (adjunctionPointsEquiv F e T).symm.trans
    ((pointsIso F e).app (op ((algΓ R).obj T))).groupIsoToMulEquiv

/-- The comparison uses the algebra map supplied by the relative adjunction. -/
theorem pointsEquiv_apply (T : Over (Spec R)) (x : T ⟶ (groupScheme F e).X) :
    pointsEquiv F e T x = e.homEquiv
      (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop := rfl

/-- Restriction of points corresponds to the map on relative global sections. -/
theorem pointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme F e).X) :
    pointsEquiv F e T' (a ≫ x) =
      F.map ((algΓ R).map a).unop (pointsEquiv F e T x) := by
  change T ⟶ (algSpec R).obj (op B) at x
  change e.homEquiv (((algΓAlgSpecAdjunction R).homEquiv T' (op B)).symm (a ≫ x)).unop =
    F.map ((algΓ R).map a).unop
      (e.homEquiv (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop)
  rw [(algΓAlgSpecAdjunction R).homEquiv_naturality_left_symm a x]
  exact e.homEquiv_comp ((algΓ R).map a).unop
    (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop

/-- The full point presheaf evaluates the original functor on relative global sections. -/
def globalPointsFunctor : (Over (Spec R))ᵒᵖ ⥤ GrpCat := (algΓ R).op ⋙ presheaf F

/-- Natural group-valued recovery on all test schemes, without affineness assumptions. -/
def globalPointsIso : GroupScheme.points (groupScheme F e) ≅ globalPointsFunctor F :=
  NatIso.ofComponents (fun T => (pointsEquiv F e T.unop).toGrpIso) (by
    intro T T' a
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact pointsEquiv_naturality F e a.unop x)

variable {F} {G : CommAlgCat R ⥤ GrpCat.{u}} {C : CommAlgCat R}
  (d : (G ⋙ forget GrpCat).CorepresentableBy C) (α : F ⟶ G)

/-- Induced scheme homomorphisms recover the original transformation on every test scheme. -/
theorem groupSchemeMap_points {T : Over (Spec R)} (x : T ⟶ (groupScheme F e).X) :
    pointsEquiv G d T (x ≫ (groupSchemeMap e d α).hom.hom) =
      α.app ((algΓ R).obj T).unop (pointsEquiv F e T x) := by
  change T ⟶ (algSpec R).obj (op B) at x
  change d.homEquiv (((algΓAlgSpecAdjunction R).homEquiv T (op C)).symm
    (x ≫ (algSpec R).map (cogroupMap e d α).hom.hom)).unop =
    α.app ((algΓ R).obj T).unop
      (e.homEquiv (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop)
  rw [(algΓAlgSpecAdjunction R).homEquiv_naturality_right_symm]
  change d.homEquiv
    (d.homEquiv.symm (α.app B (e.homEquiv (𝟙 B))) ≫
      (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop) = _
  rw [d.homEquiv_comp, Equiv.apply_symm_apply]
  let q := (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm x).unop
  have h := ConcreteCategory.congr_hom (α.naturality q) (e.homEquiv (𝟙 B))
  change α.app _ (F.map q (e.homEquiv (𝟙 B))) =
    G.map q (α.app B (e.homEquiv (𝟙 B))) at h
  change G.map q (α.app B (e.homEquiv (𝟙 B))) = α.app _ (e.homEquiv q)
  rw [← h]
  congr 1
  have h' := e.homEquiv_comp q (𝟙 B)
  rw [Category.id_comp] at h'
  exact h'.symm

end Langlands.GroupScheme.Corepresented
