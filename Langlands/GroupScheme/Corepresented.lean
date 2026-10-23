import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Group.Affine

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} (F : CommAlgCat R ⥤ GrpCat.{u}) {B : CommAlgCat R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- Regard a covariant algebra functor as a presheaf on opposite algebras. -/
abbrev presheaf : (CommAlgCat R)ᵒᵖᵒᵖ ⥤ GrpCat := unopUnop _ ⋙ F

/-- A corepresentation becomes a representation on opposite algebras. -/
def representableBy : (presheaf F ⋙ forget GrpCat).RepresentableBy (op B) where
  homEquiv :=
    { toFun := fun f => e.homEquiv f.unop
      invFun := fun x => (e.homEquiv.symm x).op
      left_inv := fun f => by simp
      right_inv := fun x => by simp }
  homEquiv_comp f g := e.homEquiv_comp f.unop g.unop

/-- The actual cogroup structure on the representing algebra. -/
abbrev cogroup : Grp (CommAlgCat R)ᵒᵖ :=
  letI := GrpObj.ofRepresentableBy (op B) (presheaf F) (representableBy F e)
  Grp.mk (op B)

/-- The cogroup's point groups recover the original functor. -/
def pointsIso : yonedaGrp.obj (cogroup F e) ≅ presheaf F :=
  yonedaGrpObjIsoOfRepresentableBy (op B) (presheaf F) (representableBy F e)

/-- The affine group scheme carried by the explicit representing algebra. -/
abbrev groupScheme : GroupScheme (Spec R) := (algSpec R).mapGrp.obj (cogroup F e)

@[simp] theorem groupScheme_X : (groupScheme F e).X = (algSpec R).obj (op B) := rfl

/-- Affine test-scheme points are the original group-valued algebra points. -/
def affinePointsEquiv (S : CommAlgCat R) :
    ((algSpec R).obj (op S) ⟶ (groupScheme F e).X) ≃* F.obj S := by
  letI := (cogroup F e).grp
  exact (algSpec.fullyFaithful.homMulEquiv (X := op S) (M := (cogroup F e).X)).symm.trans
    ((pointsIso F e).app (op (op S))).groupIsoToMulEquiv

/-- The point comparison evaluates the algebra homomorphism corresponding to the scheme map. -/
theorem affinePointsEquiv_apply (S : CommAlgCat R)
    (f : (algSpec R).obj (op S) ⟶ (groupScheme F e).X) :
    affinePointsEquiv F e S f = e.homEquiv (algSpec.fullyFaithful.preimage f).unop := rfl

/-- Specializing along a known algebra map recovers the given classification map. -/
@[simp] theorem affinePointsEquiv_map (S : CommAlgCat R) (f : B ⟶ S) :
    affinePointsEquiv F e S ((algSpec R).map f.op) = e.homEquiv f := by
  change e.homEquiv ((algSpec.fullyFaithful.preimage ((algSpec R).map f.op)).unop) = _
  rw [algSpec.fullyFaithful.preimage_map]
  rfl

/-- Affine point recovery is natural under change of test algebra. -/
theorem affinePointsEquiv_naturality {S T : CommAlgCat R} (g : S ⟶ T)
    (f : (algSpec R).obj (op S) ⟶ (groupScheme F e).X) :
    affinePointsEquiv F e T ((algSpec R).map g.op ≫ f) =
      F.map g (affinePointsEquiv F e S f) := by
  change (algSpec R).obj (op S) ⟶ (algSpec R).obj (op B) at f
  change e.homEquiv (algSpec.fullyFaithful.preimage ((algSpec R).map g.op ≫ f)).unop = _
  rw [algSpec.fullyFaithful.preimage_comp, algSpec.fullyFaithful.preimage_map]
  exact e.homEquiv_comp g (algSpec.fullyFaithful.preimage f).unop

variable {F} {G : CommAlgCat R ⥤ GrpCat.{u}} {C : CommAlgCat R}
  (d : (G ⋙ forget GrpCat).CorepresentableBy C) (α : F ⟶ G)

/-- A natural homomorphism of represented functors induces a cogroup homomorphism. -/
def cogroupMap : cogroup F e ⟶ cogroup G d :=
  yonedaGrpFullyFaithful.preimage
    ((pointsIso F e).hom ≫ Functor.whiskerLeft (unopUnop _) α ≫ (pointsIso G d).inv)

/-- Its algebra map classifies the image of the universal point. -/
theorem cogroupMap_hom :
    (cogroupMap e d α).hom.hom =
      (d.homEquiv.symm ((α.app B) (e.homEquiv (𝟙 B)))).op := rfl

/-- A natural homomorphism induces an actual homomorphism of affine group schemes. -/
def groupSchemeMap : groupScheme F e ⟶ groupScheme G d :=
  (algSpec R).mapGrp.map (cogroupMap e d α)

/-- The underlying scheme map is the spectrum of the universal classifying algebra map. -/
theorem groupSchemeMap_hom :
    (groupSchemeMap e d α).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (d.homEquiv.symm ((α.app B) (e.homEquiv (𝟙 B)))).hom.toRingHom) := rfl

/-- The induced group-scheme map recovers the original natural homomorphism on affine points. -/
theorem groupSchemeMap_affinePoints {S : CommAlgCat R}
    (f : (algSpec R).obj (op S) ⟶ (groupScheme F e).X) :
    affinePointsEquiv G d S (f ≫ (groupSchemeMap e d α).hom.hom) =
      α.app S (affinePointsEquiv F e S f) := by
  change (algSpec R).obj (op S) ⟶ (algSpec R).obj (op B) at f
  change d.homEquiv (algSpec.fullyFaithful.preimage
    (f ≫ (algSpec R).map
      (d.homEquiv.symm (α.app B (e.homEquiv (𝟙 B)))).op)).unop = _
  rw [algSpec.fullyFaithful.preimage_comp, algSpec.fullyFaithful.preimage_map]
  change d.homEquiv
    (d.homEquiv.symm (α.app B (e.homEquiv (𝟙 B))) ≫
      (algSpec.fullyFaithful.preimage f).unop) = _
  rw [d.homEquiv_comp, Equiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom (α.naturality (algSpec.fullyFaithful.preimage f).unop)
    (e.homEquiv (𝟙 B))
  change α.app S (F.map (algSpec.fullyFaithful.preimage f).unop (e.homEquiv (𝟙 B))) =
    G.map (algSpec.fullyFaithful.preimage f).unop (α.app B (e.homEquiv (𝟙 B))) at h
  change G.map (algSpec.fullyFaithful.preimage f).unop (α.app B (e.homEquiv (𝟙 B))) =
    α.app S (e.homEquiv (algSpec.fullyFaithful.preimage f).unop)
  rw [← h]
  apply congrArg (α.app S)
  have h' := e.homEquiv_comp (algSpec.fullyFaithful.preimage f).unop (𝟙 B)
  rw [Category.id_comp] at h'
  exact h'.symm

/-- Commutative point groups give a commutative affine group scheme. -/
def commGroupScheme (F : CommAlgCat R ⥤ CommGrpCat.{u}) {B : CommAlgCat R}
    (e : (F ⋙ forget CommGrpCat).CorepresentableBy B) : CommGroupScheme (Spec R) := by
  letI := CommGrpObj.ofRepresentableBy (op B) (unopUnop _ ⋙ F)
    (representableBy (F ⋙ forget₂ CommGrpCat GrpCat) e)
  exact { groupScheme (F ⋙ forget₂ CommGrpCat GrpCat) e with
    comm := Functor.isCommMonObj_obj (F := algSpec R) (M := op B) }

end Langlands.GroupScheme.Corepresented
