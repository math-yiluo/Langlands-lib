import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProduct
import Langlands.GroupScheme.Reductive.AlmostSimpleNormalSubgroup

/-! # Closed normal inclusions of actual almost-simple product factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Products

variable {S : Scheme.{u}} {I : Type u} [Finite I] (A : I → GroupScheme S)

/-- Insert one coordinate into a finite product of arbitrary group schemes. -/
def piFactorInclusionHom (i : I) : A i ⟶ pi A := by
  classical
  exact Pi.lift fun j =>
    if h : i = j then eqToHom (congrArg A h)
    else Grp.homMk (toUnit _ ≫ η[(A j).X])

@[simp] theorem piFactorInclusionHom_π_self (i : I) :
    piFactorInclusionHom A i ≫ Pi.π A i = 𝟙 (A i) := by
  classical
  simp [piFactorInclusionHom]

theorem piFactorInclusionHom_π_ne (i j : I) (h : i ≠ j) :
    piFactorInclusionHom A i ≫ Pi.π A j =
      Grp.homMk (toUnit _ ≫ η[(A j).X]) := by
  classical
  simp [piFactorInclusionHom, h]

@[simp] theorem piFactorInclusionHom_points_self (i : I) {T : Over S}
    (x : T ⟶ (A i).X) :
    (x ≫ (piFactorInclusionHom A i).hom.hom) ≫ (Pi.π A i).hom.hom = x := by
  rw [Category.assoc, ← Grp.comp_hom_hom, piFactorInclusionHom_π_self,
    Grp.id_hom_hom, Category.comp_id]

theorem piFactorInclusionHom_points_ne (i j : I) (h : i ≠ j) {T : Over S}
    (x : T ⟶ (A i).X) :
    (x ≫ (piFactorInclusionHom A i).hom.hom) ≫ (Pi.π A j).hom.hom = 1 := by
  rw [Category.assoc, ← Grp.comp_hom_hom, piFactorInclusionHom_π_ne A i j h]
  change x ≫ (1 : (A i).X ⟶ (A j).X) = 1
  exact MonObj.comp_one _

/-- An all-test point lies in one coordinate exactly when its other
coordinates are the identity. -/
theorem mem_range_piFactorInclusionHom_iff (i : I) {T : Over S}
    (x : T ⟶ (pi A).X) :
    x ∈ (SubgroupFunctor.range (piFactorInclusionHom A i)).carrier T ↔
      ∀ j, i ≠ j → x ≫ (Pi.π A j).hom.hom = 1 := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ j h
    exact piFactorInclusionHom_points_ne A i j h y
  · intro hx
    refine ⟨x ≫ (Pi.π A i).hom.hom, ?_⟩
    apply (piPointsEquiv A T).injective
    funext j
    change ((x ≫ (Pi.π A i).hom.hom) ≫
      (piFactorInclusionHom A i).hom.hom) ≫ (Pi.π A j).hom.hom =
        x ≫ (Pi.π A j).hom.hom
    by_cases h : i = j
    · subst j
      exact piFactorInclusionHom_points_self A i _
    · rw [piFactorInclusionHom_points_ne A i j h, hx j h]

/-- A coordinate is normal on every test scheme, without a commutativity
assumption on the product or its factors. -/
theorem isNormal_range_piFactorInclusionHom (i : I) :
    (SubgroupFunctor.range (piFactorInclusionHom A i)).IsNormal := by
  intro T g x _ hx
  apply (mem_range_piFactorInclusionHom_iff A i _).2
  intro j h
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    (mem_range_piFactorInclusionHom_iff A i x).1 hx j h]
  simp

end Products

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}

namespace SimplyConnectedAlmostSimpleProduct

variable (D : SimplyConnectedAlmostSimpleProduct G)

/-- The actual inclusion of a chosen product factor into the original group. -/
def inclusion (i : D.Index) : D.factor i ⟶ G :=
  piFactorInclusionHom D.factor i ≫ D.iso.inv

/-- The actual retraction from the original group to a product factor. -/
def projection (i : D.Index) : G ⟶ D.factor i :=
  D.iso.hom ≫ Pi.π D.factor i

@[simp] theorem inclusion_projection (i : D.Index) :
    D.inclusion i ≫ D.projection i = 𝟙 _ := by
  simp [inclusion, projection]

/-- Every factor is a closed subgroup of the original affine group. -/
theorem isClosedSubgroup_inclusion [IsAffineHom G.X.hom] (i : D.Index) :
    IsClosedSubgroup (D.inclusion i) := by
  change IsClosedImmersion (D.inclusion i).hom.hom.left
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have he : (D.inclusion i).hom.hom.left ≫
      (D.projection i).hom.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, inclusion_projection,
      Grp.id_hom_hom, Over.id_left]
  have : IsClosedImmersion ((D.inclusion i).hom.hom.left ≫
      (D.projection i).hom.hom.left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ (D.projection i).hom.hom.left

/-- Every factor is normal on every test scheme of the original group. -/
theorem isNormal_range_inclusion (i : D.Index) :
    (SubgroupFunctor.range (D.inclusion i)).IsNormal := by
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  have hcoord :
      ((g ≫ D.iso.hom.hom.hom) *
        (y ≫ (piFactorInclusionHom D.factor i).hom.hom) *
        (g ≫ D.iso.hom.hom.hom)⁻¹) ∈
        (SubgroupFunctor.range (piFactorInclusionHom D.factor i)).carrier T :=
    isNormal_range_piFactorInclusionHom D.factor i T _ _ (Subgroup.mem_top _)
      (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hcoord
  refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
  have he := congrArg (fun w => w ≫ D.iso.inv.hom.hom) hz
  simpa only [inclusion, Grp.comp_hom_hom, Category.assoc,
    MonObj.mul_comp, GrpObj.inv_comp, ← Grp.comp_hom_hom,
    Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using he

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
