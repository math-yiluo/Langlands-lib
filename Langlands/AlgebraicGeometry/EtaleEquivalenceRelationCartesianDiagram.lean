import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationGeometry
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-! # Cofiltered diagrams of cartesian relation morphisms -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- An actual cartesian morphism, with both of its scheme maps. -/
structure CartesianMorphism (E F : EtaleEquivalenceRelation.{u}) where
  objMap : E.U ⟶ F.U
  relMap : E.R ⟶ F.R
  isCartesian : IsCartesianHom E F objMap relMap

namespace CartesianMorphism

@[ext]
lemma ext {E F : EtaleEquivalenceRelation.{u}} {a b : CartesianMorphism E F}
    (hU : a.objMap = b.objMap) (hR : a.relMap = b.relMap) : a = b := by
  cases a
  cases b
  cases hU
  cases hR
  rfl

end CartesianMorphism

/-- Étale equivalence relations with cartesian morphisms form a category. -/
instance : Category.{u} EtaleEquivalenceRelation.{u} where
  Hom := CartesianMorphism
  id E := ⟨𝟙 E.U, 𝟙 E.R, isCartesianHom_id E⟩
  comp a b := ⟨a.objMap ≫ b.objMap, a.relMap ≫ b.relMap,
    a.isCartesian.comp b.isCartesian⟩
  id_comp a := by ext <;> apply Category.id_comp
  comp_id a := by ext <;> apply Category.comp_id
  assoc a b c := by ext <;> apply Category.assoc

@[simp]
lemma id_objMap (E : EtaleEquivalenceRelation.{u}) :
    (𝟙 E : E ⟶ E).objMap = 𝟙 E.U := rfl

@[simp]
lemma id_relMap (E : EtaleEquivalenceRelation.{u}) :
    (𝟙 E : E ⟶ E).relMap = 𝟙 E.R := rfl

@[simp]
lemma comp_objMap {E F G : EtaleEquivalenceRelation.{u}} (a : E ⟶ F) (b : F ⟶ G) :
    (a ≫ b).objMap = a.objMap ≫ b.objMap := rfl

@[simp]
lemma comp_relMap {E F G : EtaleEquivalenceRelation.{u}} (a : E ⟶ F) (b : F ⟶ G) :
    (a ≫ b).relMap = a.relMap ≫ b.relMap := rfl

/-- The object scheme of a cartesian relation diagram. -/
@[simps]
def objectFunctor : EtaleEquivalenceRelation.{u} ⥤ Scheme.{u} where
  obj E := E.U
  map a := a.objMap

/-- The arrow scheme of a cartesian relation diagram. -/
@[simps]
def relationFunctor : EtaleEquivalenceRelation.{u} ⥤ Scheme.{u} where
  obj E := E.R
  map a := a.relMap

/-- Source maps in a cartesian diagram form a natural transformation. -/
@[simps]
def sourceTransformation : relationFunctor.{u} ⟶ objectFunctor.{u} where
  app E := E.s
  naturality _ _ a := a.isCartesian.2.w

/-- Target maps in a cartesian diagram form a natural transformation. -/
@[simps]
def targetTransformation : relationFunctor.{u} ⟶ objectFunctor.{u} where
  app E := E.t
  naturality _ _ a := a.isCartesian.1

namespace CartesianDiagram

variable {I : Type u} [Category.{u} I] (D : I ⥤ EtaleEquivalenceRelation.{u}) (i : I)

/-- The diagram of all levels mapping to a fixed level. -/
@[simps!]
def above : Over i ⥤ EtaleEquivalenceRelation.{u} := Over.forget i ⋙ D

/-- Every level above `i` carries its designated comparison to `D_i`. -/
@[simps]
def comparison : above D i ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := D.map j.hom
  naturality j k a := by
    change D.map a.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
    rw [← D.map_comp, Over.w, Category.comp_id]

/-- The object-scheme comparison in the restricted diagram. -/
@[simps]
def objectComparison : above D i ⋙ objectFunctor ⟶
    (Functor.const (Over i)).obj (D.obj i).U where
  app j := (D.map j.hom).objMap
  naturality j k a := by
    have H := congrArg CartesianMorphism.objMap ((comparison D i).naturality a)
    simpa using H

/-- Cone legs remain compatible with the chosen level under restriction. -/
lemma cone_comparison (c : Cone D) (j : Over i) :
    (c.π.app j.left).objMap ≫ (D.map j.hom).objMap = (c.π.app i).objMap := by
  exact congrArg CartesianMorphism.objMap (c.w j.hom)

/-- Restricting above a level preserves a supplied object-scheme limit cone. -/
noncomputable def isLimitObjectAbove [IsCofiltered I] (c : Cone D)
    (hc : IsLimit (objectFunctor.mapCone c)) :
    IsLimit (objectFunctor.mapCone (c.whisker (Over.forget i))) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (objectFunctor.mapCone c)).symm hc

end CartesianDiagram

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
