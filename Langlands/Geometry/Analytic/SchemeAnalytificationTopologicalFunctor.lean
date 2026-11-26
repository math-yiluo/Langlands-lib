import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismProof
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The underlying topological functor of scheme analytification -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry

/-- The object property of being locally of finite type over the ground field. -/
def locallyFiniteTypeOver (K : Type u) [Field K] :
    ObjectProperty (Over (Spec (CommRingCat.of K))) :=
  fun X => LocallyOfFiniteType X.hom

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The analytification of schemes locally of finite type, valued in their
underlying topological spaces. Its arrows are the glued analytic point maps. -/
def topologicalAnalytification : (locallyFiniteTypeOver K).FullSubcategory ⥤ TopCat.{u} where
  obj X :=
    letI : LocallyOfFiniteType X.obj.hom := X.property
    TopCat.of (Space K X.obj.hom)
  map {X Y} g :=
    letI : LocallyOfFiniteType X.obj.hom := X.property
    letI : LocallyOfFiniteType Y.obj.hom := Y.property
    ConcreteCategory.ofHom (C := TopCat)
      (MorphismExistence.analytification K X.obj.hom Y.obj.hom g.hom.left (Over.w g.hom))
  map_id X := by
    let : LocallyOfFiniteType X.obj.hom := X.property
    apply TopCat.ext
    intro x
    have h := (MorphismExistence.existsUnique_isAnalytificationMap K X.obj.hom X.obj.hom
      (𝟙 X.obj.left) (Category.id_comp _)).unique
      (MorphismExistence.isAnalytificationMap_analytification K X.obj.hom X.obj.hom
        (𝟙 X.obj.left) (Category.id_comp _))
      (isAnalytificationMap_id K X.obj.hom)
    exact DFunLike.congr_fun h x
  map_comp {X Y Z} g h := by
    let : LocallyOfFiniteType X.obj.hom := X.property
    let : LocallyOfFiniteType Y.obj.hom := Y.property
    let : LocallyOfFiniteType Z.obj.hom := Z.property
    apply TopCat.ext
    intro x
    have hh := MorphismExistence.isAnalytificationMap_comp K X.obj.hom Y.obj.hom Z.obj.hom
      g.hom.left (Over.w g.hom) h.hom.left (Over.w h.hom) _ _
      (MorphismExistence.isAnalytificationMap_analytification K X.obj.hom Y.obj.hom
        g.hom.left (Over.w g.hom))
      (MorphismExistence.isAnalytificationMap_analytification K Y.obj.hom Z.obj.hom
        h.hom.left (Over.w h.hom))
    have e := (MorphismExistence.existsUnique_isAnalytificationMap K X.obj.hom Z.obj.hom
      (g.hom.left ≫ h.hom.left) (Over.w (g.hom ≫ h.hom))).unique
      (MorphismExistence.isAnalytificationMap_analytification K X.obj.hom Z.obj.hom
        (g.hom.left ≫ h.hom.left) (Over.w (g.hom ≫ h.hom))) hh
    exact DFunLike.congr_fun e x

/-- The continuous center maps are natural in all scheme morphisms over the field. -/
def analytificationCenterNatTrans : topologicalAnalytification K ⟶
    ObjectProperty.ι (locallyFiniteTypeOver K) ⋙ Over.forget _ ⋙ Scheme.forgetToTop where
  app X :=
    letI : LocallyOfFiniteType X.obj.hom := X.property
    ConcreteCategory.ofHom (C := TopCat) (center K X.obj.hom)
  naturality {X Y} g := by
    let : LocallyOfFiniteType X.obj.hom := X.property
    let : LocallyOfFiniteType Y.obj.hom := Y.property
    apply TopCat.ext
    intro x
    exact ((MorphismCompatibility.compatibility K X.obj.hom Y.obj.hom
      g.hom.left (Over.w g.hom) _
      (MorphismExistence.isAnalytificationMap_analytification K X.obj.hom Y.obj.hom
        g.hom.left (Over.w g.hom))).1 x)

end Langlands.Analytic.SchemeAnalytification
