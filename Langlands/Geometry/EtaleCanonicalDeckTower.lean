import Langlands.Geometry.EtaleCanonicalCoefficientDiagram
import Langlands.Geometry.EtaleGeometricActionReindex
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Canonical coefficients and cohomology of actual over-base deck towers -/

noncomputable section

universe u v w v' w' t t' wS wR

set_option autoImplicit false

namespace Langlands.Geometry.EtaleCanonicalDeckTower

open CategoryTheory AlgebraicGeometry
open EtaleGeometricDiagram EtaleDerivedSections EtaleInverseImage
open scoped CategoryTheory.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} {J : Type v} [Category.{w} J]
variable {G : Type t} [Group G]
variable (R : Type u) [CommRing R] (A : J ⥤ Action ((Over X)ᵒᵖ) G)

/-- Uncurry actual over-base actions and their equivariant level maps. -/
def overDiagram : (J × SingleObj G) ⥤ (Over X)ᵒᵖ :=
  Functor.uncurry.obj (A ⋙ (Action.functorCategoryEquivalence ((Over X)ᵒᵖ) G).functor)

/-- Forget only the over-base packaging, retaining every original scheme map. -/
def schemeDiagram : (J × SingleObj G) ⥤ Scheme.{u}ᵒᵖ :=
  overDiagram A ⋙ (Over.forget X).op

/-- The original structure maps give a natural projection from every level
and every group translate to the same base. -/
def projection :
    (Functor.const (J × SingleObj G)).obj (Opposite.op X) ⟶ schemeDiagram A where
  app x := ((overDiagram A).obj x).unop.hom.op
  naturality x y a := by
    apply Quiver.Hom.unop_inj
    change ((overDiagram A).obj y).unop.hom ≫ 𝟙 X =
      (((overDiagram A).map a).unop).left ≫ ((overDiagram A).obj x).unop.hom
    rw [Category.comp_id]
    exact (Over.w (((overDiagram A).map a).unop)).symm

/-- The actual scheme at a level is the original source over the base. -/
@[simp] theorem schemeDiagram_obj (x : J × SingleObj G) :
    ((schemeDiagram A).obj x).unop = (A.obj x.1).V.unop.left := rfl

/-- The projection is precisely the original over-object's structure map. -/
@[simp] theorem projection_app (x : J × SingleObj G) :
    ((projection A).app x).unop = (A.obj x.1).V.unop.hom := rfl

/-- A general product arrow first uses the original group map on the source
scheme, then the original contravariant level map. -/
theorem schemeDiagram_map {x y : J × SingleObj G} (a : x ⟶ y) :
    ((schemeDiagram A).map a).unop =
      ((A.obj y.1).ρ a.2).unop.left ≫ (A.map a.1).hom.unop.left := rfl

/-- Pure group arrows recover the original geometric deck maps. -/
@[simp] theorem schemeDiagram_map_group (i : J) (g : G) :
    ((schemeDiagram A).map (X := (i, SingleObj.star G)) (Y := (i, SingleObj.star G))
      (𝟙 i ×ₘ g)).unop =
      ((A.obj i).ρ g).unop.left := by
  rw [schemeDiagram_map, A.map_id]
  simp

/-- Pure level arrows recover the original geometric level maps. -/
@[simp] theorem schemeDiagram_map_level {i j : J} (a : i ⟶ j) :
    ((schemeDiagram A).map (a ×ₘ 𝟙 (SingleObj.star G))).unop =
      (A.map a).hom.unop.left := by
  rw [schemeDiagram_map]
  change ((A.obj j).ρ 1).unop.left ≫ _ = _
  rw [(A.obj j).ρ.map_one]
  simp

/-- Original deck maps are automorphisms because the input is a group action. -/
instance groupMap_isIso (i : J) (g : G) :
    IsIso (((A.obj i).ρ g).unop.left) := by
  let e := ((A.obj i).ρAut g).unop
  exact (Over.forget X).map_isIso e.hom

/-- The original over-base group triangle supplies the coefficient comparison. -/
def groupCoefficientIso (i : J) (g : G) :
    inverseImage (A.obj i).V.unop.hom R ⋙
        inverseImage ((A.obj i).ρ g).unop.left R ≅
      inverseImage (A.obj i).V.unop.hom R :=
  projectionInverseImageIso R _ _ _ (Over.w ((A.obj i).ρ g).unop)

/-- The original over-base level triangle supplies the coefficient comparison. -/
def levelCoefficientIso {i j : J} (a : i ⟶ j) :
    inverseImage (A.obj i).V.unop.hom R ⋙
        inverseImage (A.map a).hom.unop.left R ≅
      inverseImage (A.obj j).V.unop.hom R :=
  projectionInverseImageIso R _ _ _ (Over.w (A.map a).hom.unop)

/-- All original base coefficients and all their morphisms pull back
canonically along this actual geometric deck tower. -/
def coefficientFunctor :
    ModuleSheaf X R ⥤ CoefficientDiagram R (schemeDiagram A) :=
  canonicalCoefficientsFunctor R (projection A)

/-- At every product vertex the coefficient is the original inverse image. -/
@[simp] theorem coefficientFunctor_obj_obj (M : ModuleSheaf X R)
    (x : J × SingleObj G) :
    ((coefficientFunctor R A).obj M).obj x =
      (inverseImage (A.obj x.1).V.unop.hom R).obj M := rfl

/-- Transition coefficients use the actual composition comparison followed by
the literal over-base triangle equality. -/
theorem coefficientFunctor_obj_map (M : ModuleSheaf X R)
    {x y : J × SingleObj G} (a : x ⟶ y) :
    ((coefficientFunctor R A).obj M).map a =
      (projectionInverseImageIso R (A.obj x.1).V.unop.hom
        (A.obj y.1).V.unop.hom ((schemeDiagram A).map a).unop
        (baseProjection_triangle (projection A) a)).hom.app M := rfl

/-- Every coefficient morphism is the original inverse image at each vertex. -/
@[simp] theorem coefficientFunctor_map_app {M N : ModuleSheaf X R}
    (α : M ⟶ N) (x : J × SingleObj G) :
    ((coefficientFunctor R A).map α).app x =
      (inverseImage (A.obj x.1).V.unop.hom R).map α := rfl

section ReindexGeometry

variable {K : Type v'} [Category.{w'} K] {H : Type t'} [Group H]
variable (F : K ⥤ J) (φ : H →* G)

/-- Select original levels and restrict their actual over-base actions. -/
def reindex : K ⥤ Action ((Over X)ᵒᵖ) H :=
  (actionDiagramReindexFunctor F φ ((Over X)ᵒᵖ)).obj A

/-- Reindexing retains the original product-index scheme diagram. -/
theorem schemeDiagram_reindex :
    schemeDiagram (reindex A F φ) =
      (F.prod (SingleObj.mapHom H G φ)) ⋙ schemeDiagram A := rfl

/-- The reindexed projection retains the original structure maps. -/
theorem projection_reindex :
    projection (reindex A F φ) =
      reindexBaseProjection (projection A) (F.prod (SingleObj.mapHom H G φ)) := rfl

/-- Canonical base coefficients commute with actual level and group
reindexing, naturally in every original base sheaf and morphism. -/
def reindexCoefficientFunctorIso :
    coefficientFunctor R (reindex A F φ) ≅
      coefficientFunctor R A ⋙
        CoefficientDiagram.reindexFunctor (F.prod (SingleObj.mapHom H G φ)) :=
  (canonicalCoefficientsReindexIso R (projection A)
    (F.prod (SingleObj.mapHom H G φ))).symm

/-- The coefficient reindex comparison has identity original-sheaf components. -/
@[simp] theorem reindexCoefficientFunctorIso_hom_app_app
    (M : ModuleSheaf X R) (x : K × SingleObj H) :
    ((reindexCoefficientFunctorIso R A F φ).hom.app M).app x = 𝟙 _ := rfl

@[simp] theorem reindexCoefficientFunctorIso_inv_app_app
    (M : ModuleSheaf X R) (x : K × SingleObj H) :
    ((reindexCoefficientFunctorIso R A F φ).inv.app M).app x = 𝟙 _ := rfl

end ReindexGeometry

section Cohomology

variable [∀ x : J × SingleObj G,
  HasDerivedCategory.{wS} (ModuleSheaf ((schemeDiagram A).obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance (i : J) :
    HasDerivedCategory.{wS} (ModuleSheaf (A.obj i).V.unop.left R) :=
  inferInstanceAs (HasDerivedCategory.{wS}
    (ModuleSheaf ((schemeDiagram A).obj (i, SingleObj.star G)).unop R))

/-- Derived global sections with actions and level maps constructed from
the original deck geometry, natural in every original base coefficient. -/
def derivedFunctor :
    ModuleSheaf X R ⥤ (J ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G) :=
  coefficientFunctor R A ⋙ CoefficientDiagram.derivedActionFunctor

/-- Ordinary cohomology of all canonical inverse-image coefficients. -/
def cohomologyFunctor (q : ℕ) :
    ModuleSheaf X R ⥤ (J ⥤ Action (ModuleCat.{u} R) G) :=
  coefficientFunctor R A ⋙ CoefficientDiagram.cohomologyActionFunctor q

/-- Actual global sections with the same original deck and level maps. -/
def sectionsFunctor :
    ModuleSheaf X R ⥤ (J ⥤ Action (ModuleCat.{u} R) G) :=
  coefficientFunctor R A ⋙ CoefficientDiagram.sectionsActionFunctor

/-- The underlying derived object uses the actual original scheme and sheaf. -/
@[simp] theorem derivedFunctor_obj_obj_V (M : ModuleSheaf X R) (i : J) :
    (((derivedFunctor R A).obj M).obj i).V =
      (EtaleDerivedSectionsPlus.derivedSections (A.obj i).V.unop.left R).obj
        ((inverseImage (A.obj i).V.unop.hom R).obj M) := rfl

/-- The ordinary object is actual cohomology of the pulled-back base sheaf. -/
@[simp] theorem cohomologyFunctor_obj_obj_V (q : ℕ) (M : ModuleSheaf X R) (i : J) :
    (((cohomologyFunctor R A q).obj M).obj i).V =
      (EtaleDerivedSections.cohomology (A.obj i).V.unop.left R q).obj
        ((inverseImage (A.obj i).V.unop.hom R).obj M) := rfl

/-- The section object is the original global-section module. -/
@[simp] theorem sectionsFunctor_obj_obj_V (M : ModuleSheaf X R) (i : J) :
    (((sectionsFunctor R A).obj M).obj i).V =
      (EtaleDerivedSections.sections (A.obj i).V.unop.left R).obj
        ((inverseImage (A.obj i).V.unop.hom R).obj M) := rfl

/-- The derived action is pullback along the original deck automorphism. -/
theorem derivedFunctor_obj_obj_ρ (M : ModuleSheaf X R) (i : J) (g : G) :
    (((derivedFunctor R A).obj M).obj i).ρ g =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients
        ((A.obj i).ρ g).unop.left R ((groupCoefficientIso R A i g).hom.app M) := by
  change EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients
    (X := (A.obj i).V.unop.left) (Z := (A.obj i).V.unop.left)
    ((schemeDiagram A).map (𝟙 i ×ₘ g)).unop R
      ((projectionInverseImageIso R (A.obj i).V.unop.hom
        (A.obj i).V.unop.hom _
        (baseProjection_triangle (projection A) (𝟙 i ×ₘ g))).hom.app M) = _
  let T := {f : (A.obj i).V.unop.left ⟶ (A.obj i).V.unop.left //
    f ≫ (A.obj i).V.unop.hom = (A.obj i).V.unop.hom}
  have h : (⟨((schemeDiagram A).map (𝟙 i ×ₘ g)).unop,
      baseProjection_triangle (projection A) (𝟙 i ×ₘ g)⟩ : T) =
      ⟨((A.obj i).ρ g).unop.left, (Over.w ((A.obj i).ρ g).unop)⟩ :=
    Subtype.ext (schemeDiagram_map_group A i g)
  have result := congrArg
    (fun f : T => EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f.val R
      ((projectionInverseImageIso R _ _ f.val f.property).hom.app M)) h
  exact result

/-- The derived level map is pullback along the original level morphism. -/
theorem derivedFunctor_obj_map_hom (M : ModuleSheaf X R)
    {i j : J} (a : i ⟶ j) :
    (((derivedFunctor R A).obj M).map a).hom =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients
        (A.map a).hom.unop.left R ((levelCoefficientIso R A a).hom.app M) := by
  change EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients
    (X := (A.obj i).V.unop.left) (Z := (A.obj j).V.unop.left)
    ((schemeDiagram A).map (a ×ₘ 𝟙 (SingleObj.star G))).unop R
      ((projectionInverseImageIso R (A.obj i).V.unop.hom
        (A.obj j).V.unop.hom _
        (baseProjection_triangle (projection A)
          (a ×ₘ 𝟙 (SingleObj.star G)))).hom.app M) = _
  let T := {f : (A.obj j).V.unop.left ⟶ (A.obj i).V.unop.left //
    f ≫ (A.obj i).V.unop.hom = (A.obj j).V.unop.hom}
  have h : (⟨((schemeDiagram A).map (a ×ₘ 𝟙 (SingleObj.star G))).unop,
      baseProjection_triangle (projection A) (a ×ₘ 𝟙 (SingleObj.star G))⟩ : T) =
      ⟨(A.map a).hom.unop.left, (Over.w (A.map a).hom.unop)⟩ :=
    Subtype.ext (schemeDiagram_map_level A a)
  have result := congrArg
    (fun f : T => EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f.val R
      ((projectionInverseImageIso R _ _ f.val f.property).hom.app M)) h
  exact result

/-- Every base-sheaf morphism acts by derived sections of its inverse image. -/
@[simp] theorem derivedFunctor_map_app_hom {M N : ModuleSheaf X R}
    (α : M ⟶ N) (i : J) :
    (((derivedFunctor R A).map α).app i).hom =
      (EtaleDerivedSectionsPlus.derivedSections (A.obj i).V.unop.left R).map
        ((inverseImage (A.obj i).V.unop.hom R).map α) := rfl

/-- The ordinary action is pullback along the original deck automorphism. -/
theorem cohomologyFunctor_obj_obj_ρ (q : ℕ) (M : ModuleSheaf X R) (i : J) (g : G) :
    (((cohomologyFunctor R A q).obj M).obj i).ρ g =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients
        ((A.obj i).ρ g).unop.left R q ((groupCoefficientIso R A i g).hom.app M) := by
  change ((((coefficientFunctor R A).obj M).cohomologyAction q).obj i).ρ g = _
  rw [CoefficientDiagram.cohomologyAction_obj_ρ]
  change EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients
    (X := (A.obj i).V.unop.left) (Z := (A.obj i).V.unop.left)
    ((schemeDiagram A).map (𝟙 i ×ₘ g)).unop R q
      ((projectionInverseImageIso R (A.obj i).V.unop.hom
        (A.obj i).V.unop.hom _
        (baseProjection_triangle (projection A) (𝟙 i ×ₘ g))).hom.app M) = _
  let T := {f : (A.obj i).V.unop.left ⟶ (A.obj i).V.unop.left //
    f ≫ (A.obj i).V.unop.hom = (A.obj i).V.unop.hom}
  have h : (⟨((schemeDiagram A).map (𝟙 i ×ₘ g)).unop,
      baseProjection_triangle (projection A) (𝟙 i ×ₘ g)⟩ : T) =
      ⟨((A.obj i).ρ g).unop.left, (Over.w ((A.obj i).ρ g).unop)⟩ :=
    Subtype.ext (schemeDiagram_map_group A i g)
  have result := congrArg
    (fun f : T => EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f.val R q
      ((projectionInverseImageIso R _ _ f.val f.property).hom.app M)) h
  exact result

/-- The ordinary level map is pullback along the original level morphism. -/
theorem cohomologyFunctor_obj_map_hom (q : ℕ) (M : ModuleSheaf X R)
    {i j : J} (a : i ⟶ j) :
    (((cohomologyFunctor R A q).obj M).map a).hom =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients
        (A.map a).hom.unop.left R q ((levelCoefficientIso R A a).hom.app M) := by
  change ((((coefficientFunctor R A).obj M).cohomologyAction q).map a).hom = _
  rw [CoefficientDiagram.cohomologyAction_map_hom]
  change EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients
    (X := (A.obj i).V.unop.left) (Z := (A.obj j).V.unop.left)
    ((schemeDiagram A).map (a ×ₘ 𝟙 (SingleObj.star G))).unop R q
      ((projectionInverseImageIso R (A.obj i).V.unop.hom
        (A.obj j).V.unop.hom _
        (baseProjection_triangle (projection A)
          (a ×ₘ 𝟙 (SingleObj.star G)))).hom.app M) = _
  let T := {f : (A.obj j).V.unop.left ⟶ (A.obj i).V.unop.left //
    f ≫ (A.obj i).V.unop.hom = (A.obj j).V.unop.hom}
  have h : (⟨((schemeDiagram A).map (a ×ₘ 𝟙 (SingleObj.star G))).unop,
      baseProjection_triangle (projection A) (a ×ₘ 𝟙 (SingleObj.star G))⟩ : T) =
      ⟨(A.map a).hom.unop.left, (Over.w (A.map a).hom.unop)⟩ :=
    Subtype.ext (schemeDiagram_map_level A a)
  have result := congrArg
    (fun f : T => EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f.val R q
      ((projectionInverseImageIso R _ _ f.val f.property).hom.app M)) h
  exact result

/-- Every base-sheaf morphism acts by cohomology of its inverse image. -/
@[simp] theorem cohomologyFunctor_map_app_hom (q : ℕ) {M N : ModuleSheaf X R}
    (α : M ⟶ N) (i : J) :
    (((cohomologyFunctor R A q).map α).app i).hom =
      (EtaleDerivedSections.cohomology (A.obj i).V.unop.left R q).map
        ((inverseImage (A.obj i).V.unop.hom R).map α) := rfl

/-- The section action is pullback along the original deck automorphism. -/
theorem sectionsFunctor_obj_obj_ρ (M : ModuleSheaf X R) (i : J) (g : G) :
    (((sectionsFunctor R A).obj M).obj i).ρ g =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients
        ((A.obj i).ρ g).unop.left R ((groupCoefficientIso R A i g).hom.app M) := by
  change ((((coefficientFunctor R A).obj M).sectionsAction).obj i).ρ g = _
  rw [CoefficientDiagram.sectionsAction_obj_ρ]
  change EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients
    (X := (A.obj i).V.unop.left) (Z := (A.obj i).V.unop.left)
    ((schemeDiagram A).map (𝟙 i ×ₘ g)).unop R
      ((projectionInverseImageIso R (A.obj i).V.unop.hom
        (A.obj i).V.unop.hom _
        (baseProjection_triangle (projection A) (𝟙 i ×ₘ g))).hom.app M) = _
  let T := {f : (A.obj i).V.unop.left ⟶ (A.obj i).V.unop.left //
    f ≫ (A.obj i).V.unop.hom = (A.obj i).V.unop.hom}
  have h : (⟨((schemeDiagram A).map (𝟙 i ×ₘ g)).unop,
      baseProjection_triangle (projection A) (𝟙 i ×ₘ g)⟩ : T) =
      ⟨((A.obj i).ρ g).unop.left, (Over.w ((A.obj i).ρ g).unop)⟩ :=
    Subtype.ext (schemeDiagram_map_group A i g)
  have result := congrArg
    (fun f : T => EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f.val R
      ((projectionInverseImageIso R _ _ f.val f.property).hom.app M)) h
  exact result

/-- The section level map is pullback along the original level morphism. -/
theorem sectionsFunctor_obj_map_hom (M : ModuleSheaf X R)
    {i j : J} (a : i ⟶ j) :
    (((sectionsFunctor R A).obj M).map a).hom =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients
        (A.map a).hom.unop.left R ((levelCoefficientIso R A a).hom.app M) := by
  change ((((coefficientFunctor R A).obj M).sectionsAction).map a).hom = _
  rw [CoefficientDiagram.sectionsAction_map_hom]
  change EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients
    (X := (A.obj i).V.unop.left) (Z := (A.obj j).V.unop.left)
    ((schemeDiagram A).map (a ×ₘ 𝟙 (SingleObj.star G))).unop R
      ((projectionInverseImageIso R (A.obj i).V.unop.hom
        (A.obj j).V.unop.hom _
        (baseProjection_triangle (projection A)
          (a ×ₘ 𝟙 (SingleObj.star G)))).hom.app M) = _
  let T := {f : (A.obj j).V.unop.left ⟶ (A.obj i).V.unop.left //
    f ≫ (A.obj i).V.unop.hom = (A.obj j).V.unop.hom}
  have h : (⟨((schemeDiagram A).map (a ×ₘ 𝟙 (SingleObj.star G))).unop,
      baseProjection_triangle (projection A) (a ×ₘ 𝟙 (SingleObj.star G))⟩ : T) =
      ⟨(A.map a).hom.unop.left, (Over.w (A.map a).hom.unop)⟩ :=
    Subtype.ext (schemeDiagram_map_level A a)
  have result := congrArg
    (fun f : T => EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f.val R
      ((projectionInverseImageIso R _ _ f.val f.property).hom.app M)) h
  exact result

/-- Every base-sheaf morphism acts by sections of its inverse image. -/
@[simp] theorem sectionsFunctor_map_app_hom {M N : ModuleSheaf X R}
    (α : M ⟶ N) (i : J) :
    (((sectionsFunctor R A).map α).app i).hom =
      (EtaleDerivedSections.sections (A.obj i).V.unop.left R).map
        ((inverseImage (A.obj i).V.unop.hom R).map α) := rfl

/-- Homology recovers ordinary cohomology, naturally in all base sheaves
and equivariantly along every level. -/
def homologyFunctorIso (q : ℕ) :
    derivedFunctor R A ⋙
        (Functor.whiskeringRight J (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G) ≅
      cohomologyFunctor R A q :=
  Functor.isoWhiskerLeft (coefficientFunctor R A)
    (CoefficientDiagram.derivedActionHomologyFunctorIso q)

/-- Degree-zero derived recovery uses the original canonical section comparison. -/
def derivedZeroFunctorIso :
    derivedFunctor R A ⋙
        (Functor.whiskeringRight J (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≅
      sectionsFunctor R A :=
  Functor.isoWhiskerLeft (coefficientFunctor R A)
    CoefficientDiagram.derivedActionZeroFunctorIso

/-- Ordinary degree-zero recovery is likewise natural in every base coefficient. -/
def cohomologyZeroFunctorIso :
    cohomologyFunctor R A 0 ≅ sectionsFunctor R A :=
  Functor.isoWhiskerLeft (coefficientFunctor R A)
    CoefficientDiagram.cohomologyActionZeroFunctorIso

/-- Homology recovery retains the canonical original-scheme comparison. -/
@[simp] theorem homologyFunctorIso_hom_app_app_hom
    (q : ℕ) (M : ModuleSheaf X R) (i : J) :
    (((homologyFunctorIso R A q).hom.app M).app i).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso (A.obj i).V.unop.left R q).hom.app
        ((inverseImage (A.obj i).V.unop.hom R).obj M) := rfl

/-- Derived degree-zero recovery retains the canonical section comparison. -/
@[simp] theorem derivedZeroFunctorIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : J) :
    (((derivedZeroFunctorIso R A).hom.app M).app i).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso (A.obj i).V.unop.left R).hom.app
        ((inverseImage (A.obj i).V.unop.hom R).obj M) := rfl

/-- Ordinary degree-zero recovery is the canonical homology inverse followed
by the canonical section comparison. -/
@[simp] theorem cohomologyZeroFunctorIso_hom_app_app_hom
    (M : ModuleSheaf X R) (i : J) :
    (((cohomologyZeroFunctorIso R A).hom.app M).app i).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso (A.obj i).V.unop.left R 0).inv.app
          ((inverseImage (A.obj i).V.unop.hom R).obj M) ≫
        (EtaleDerivedSectionsPlus.homologyZeroIso (A.obj i).V.unop.left R).hom.app
          ((inverseImage (A.obj i).V.unop.hom R).obj M) := rfl


end Cohomology

end Langlands.Geometry.EtaleCanonicalDeckTower
