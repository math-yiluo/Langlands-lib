/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Order.Category.PartOrdEmb
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Inverse systems and strict refinements

Source: Stacks Project, Sites, the refinement relation preceding Tag 00YO
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A diagram indexed by a small partially ordered set. -/
structure PointSystemDiagram (C : Type u) [Category.{v} C] where
  index : PartOrdEmb.{w}
  diagram : index ⥤ C

namespace PointSystemDiagram

variable {C : Type u} [Category.{v} C]

/-- A strict refinement preserves the objects and transition maps. -/
@[ext]
structure Hom (X Y : PointSystemDiagram.{u, v, w} C) where
  embedding : X.index ⟶ Y.index
  restriction : X.diagram = embedding.hom.monotone.functor ⋙ Y.diagram

instance : Category (PointSystemDiagram.{u, v, w} C) where
  Hom := Hom
  id X := ⟨𝟙 _, Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    congr 1)⟩
  comp f g := ⟨f.embedding ≫ g.embedding,
    f.restriction.trans (by rw [g.restriction]; rfl)⟩
  id_comp f := Hom.ext (Category.id_comp f.embedding)
  comp_id f := Hom.ext (Category.comp_id f.embedding)
  assoc f g h := Hom.ext (Category.assoc f.embedding g.embedding h.embedding)

/-- The index poset of a diagram. -/
@[simps]
def indexFunctor : PointSystemDiagram.{u, v, w} C ⥤ PartOrdEmb.{w} where
  obj X := X.index
  map f := f.embedding

variable {A : Type w} [SmallCategory A] [IsFiltered A]
  (F : A ⥤ PointSystemDiagram.{u, v, w} C)

/-- The colimit of the index posets. -/
noncomputable def unionIndex : PartOrdEmb.{w} := colimit (F ⋙ indexFunctor)

/-- The inclusion of a stage's index into the union. -/
noncomputable def unionEmbedding (a : A) : (F.obj a).index ⟶ unionIndex F :=
  colimit.ι (F ⋙ indexFunctor) a

/-- Every index in the union comes from a stage. -/
theorem unionEmbedding_jointly_surjective (i : unionIndex F) :
    ∃ (a : A) (j : (F.obj a).index), unionEmbedding F a j = i :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget PartOrdEmb) (colimit.isColimit (F ⋙ indexFunctor))) i

/-- Compatible object assignments on the stages. -/
def objectCocone : (F ⋙ indexFunctor ⋙ forget PartOrdEmb).CoconeTypes where
  pt := C
  ι a := (F.obj a).diagram.obj
  ι_naturality f := by
    funext i
    exact (congrArg (fun T ↦ T.obj i) (F.map f).restriction).symm

/-- The object assignment on the union, obtained by descent from the stages. -/
noncomputable def unionObject : unionIndex F → C :=
  ((Types.isColimit_iff_coconeTypesIsColimit _).mp
    ⟨isColimitOfPreserves (forget PartOrdEmb)
      (colimit.isColimit (F ⋙ indexFunctor))⟩).desc (objectCocone F)

@[simp] theorem unionObject_embedding (a : A) (i : (F.obj a).index) :
    unionObject F (unionEmbedding F a i) = (F.obj a).diagram.obj i :=
  Functor.CoconeTypes.IsColimit.fac_apply _ _ _ _

@[simp] theorem unionEmbedding_naturality {a b : A} (f : a ⟶ b)
    (i : (F.obj a).index) :
    unionEmbedding F b ((F.map f).embedding i) = unionEmbedding F a i :=
  ConcreteCategory.congr_hom (colimit.w (F ⋙ indexFunctor) f) i

/-- Any ordered pair in the union is represented by an ordered pair in one stage. -/
theorem union_le_rep {i j : unionIndex F} (h : i ≤ j) :
    ∃ (a : A) (x y : (F.obj a).index),
      unionEmbedding F a x = i ∧ unionEmbedding F a y = j ∧ x ≤ y := by
  obtain ⟨a, x, y, rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves (forget PartOrdEmb)
        (colimit.isColimit (F ⋙ indexFunctor))) i j
  exact ⟨a, x, y, rfl, rfl, (unionEmbedding F a).hom.le_iff_le.mp h⟩

/-- The map of a stage's diagram, transported to the objects of the union. -/
noncomputable def stageMap (a : A) (x y : (F.obj a).index) (h : x ≤ y) :
    unionObject F (unionEmbedding F a x) ⟶ unionObject F (unionEmbedding F a y) :=
  eqToHom (unionObject_embedding F a x) ≫
    (F.obj a).diagram.map (homOfLE h) ≫ eqToHom (unionObject_embedding F a y).symm

/-- Functoriality transports a local transition map unchanged to a later stage. -/
theorem stageMap_naturality {a b : A} (f : a ⟶ b)
    (x y : (F.obj a).index) (h : x ≤ y) :
    stageMap F a x y h =
      eqToHom (congrArg (unionObject F) (unionEmbedding_naturality F f x).symm) ≫
        stageMap F b ((F.map f).embedding x) ((F.map f).embedding y)
          ((F.map f).embedding.hom.monotone h) ≫
        eqToHom (congrArg (unionObject F) (unionEmbedding_naturality F f y)) := by
  dsimp only [stageMap]
  have hm := Functor.congr_hom (F.map f).restriction (homOfLE h)
  dsimp only [Functor.comp_map] at hm
  rw [hm]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc, eqToHom_trans]
  rfl

/-- Transporting an ordered pair along equalities does not change its local map. -/
theorem stageMap_congr (a : A) {x x' y y' : (F.obj a).index}
    (hx : x = x') (hy : y = y') (h : x ≤ y) (h' : x' ≤ y') :
    stageMap F a x y h =
      eqToHom (congrArg (fun z ↦ unionObject F (unionEmbedding F a z)) hx) ≫
        stageMap F a x' y' h' ≫
        eqToHom (congrArg (fun z ↦ unionObject F (unionEmbedding F a z)) hy.symm) := by
  subst x'
  subst y'
  simp

/-- Two stage descriptions of a transition induce the same map in the union. -/
theorem stageMap_eq_of_eq (a b : A) (x y : (F.obj a).index) (x' y' : (F.obj b).index)
    (hx : unionEmbedding F a x = unionEmbedding F b x')
    (hy : unionEmbedding F a y = unionEmbedding F b y')
    (h : x ≤ y) (h' : x' ≤ y') :
    stageMap F a x y h =
      eqToHom (congrArg (unionObject F) hx) ≫ stageMap F b x' y' h' ≫
        eqToHom (congrArg (unionObject F) hy.symm) := by
  let d := IsFiltered.max a b
  let f : a ⟶ d := IsFiltered.leftToMax a b
  let g : b ⟶ d := IsFiltered.rightToMax a b
  have hx' : (F.map f).embedding x = (F.map g).embedding x' := by
    apply (unionEmbedding F d).injective
    simpa only [unionEmbedding_naturality] using hx
  have hy' : (F.map f).embedding y = (F.map g).embedding y' := by
    apply (unionEmbedding F d).injective
    simpa only [unionEmbedding_naturality] using hy
  rw [stageMap_naturality F f, stageMap_naturality F g,
    stageMap_congr F d hx' hy' _ ((F.map g).embedding.hom.monotone h')]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc, eqToHom_trans]

/-- A stage representing one ordered pair in the union. -/
structure TransitionRep (i j : unionIndex F) where
  stage : A
  left : (F.obj stage).index
  right : (F.obj stage).index
  left_eq : unionEmbedding F stage left = i
  right_eq : unionEmbedding F stage right = j
  le : left ≤ right

theorem transitionRep_nonempty {i j : unionIndex F} (h : i ≤ j) :
    Nonempty (TransitionRep F i j) := by
  obtain ⟨a, x, y, hx, hy, hxy⟩ := union_le_rep F h
  exact ⟨⟨a, x, y, hx, hy, hxy⟩⟩

/-- A representing transition map, with its endpoints transported into the union. -/
noncomputable def TransitionRep.hom {i j : unionIndex F} (r : TransitionRep F i j) :
    unionObject F i ⟶ unionObject F j :=
  eqToHom (congrArg (unionObject F) r.left_eq.symm) ≫
    stageMap F r.stage r.left r.right r.le ≫
      eqToHom (congrArg (unionObject F) r.right_eq)

/-- The transition map on the union index. -/
noncomputable def unionMap {i j : unionIndex F} (h : i ≤ j) :
    unionObject F i ⟶ unionObject F j :=
  (Classical.choice (transitionRep_nonempty F h)).hom F

/-- A union transition can be computed in any stage containing both endpoints. -/
theorem unionMap_embedding (a : A) (x y : (F.obj a).index) (h : x ≤ y) :
    unionMap F ((unionEmbedding F a).hom.monotone h) = stageMap F a x y h := by
  let r := Classical.choice
    (transitionRep_nonempty F ((unionEmbedding F a).hom.monotone h))
  change r.hom F = _
  dsimp only [TransitionRep.hom]
  rw [stageMap_eq_of_eq F r.stage a r.left r.right x y r.left_eq r.right_eq r.le h]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- Three union indices can be represented simultaneously in one stage. -/
theorem union_triple_rep (i j k : unionIndex F) :
    ∃ (a : A) (x y z : (F.obj a).index),
      unionEmbedding F a x = i ∧ unionEmbedding F a y = j ∧
        unionEmbedding F a z = k := by
  obtain ⟨a, x, y, hx, hy⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves (forget PartOrdEmb)
        (colimit.isColimit (F ⋙ indexFunctor))) i j
  obtain ⟨b, z, hz⟩ := unionEmbedding_jointly_surjective F k
  let d := IsFiltered.max a b
  let f : a ⟶ d := IsFiltered.leftToMax a b
  let g : b ⟶ d := IsFiltered.rightToMax a b
  exact ⟨d, (F.map f).embedding x, (F.map f).embedding y, (F.map g).embedding z,
    (unionEmbedding_naturality F f x).trans hx,
    (unionEmbedding_naturality F f y).trans hy,
    (unionEmbedding_naturality F g z).trans hz⟩

/-- The compatible stage diagrams glue to a diagram on their union index. -/
noncomputable def unionDiagram : unionIndex F ⥤ C where
  obj := unionObject F
  map f := unionMap F (leOfHom f)
  map_id i := by
    obtain ⟨a, x, rfl⟩ := unionEmbedding_jointly_surjective F i
    rw [unionMap_embedding F a x x le_rfl]
    simp [stageMap]
  map_comp {i j k} f g := by
    obtain ⟨a, x, y, z, rfl, rfl, rfl⟩ := union_triple_rep F i j k
    have hxy := (unionEmbedding F a).hom.le_iff_le.mp (leOfHom f)
    have hyz := (unionEmbedding F a).hom.le_iff_le.mp (leOfHom g)
    rw [unionMap_embedding F a x z (hxy.trans hyz),
      unionMap_embedding F a x y hxy, unionMap_embedding F a y z hyz]
    simp only [stageMap, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [← Functor.map_comp_assoc]
    rfl

/-- Every original stage is strictly preserved by the union diagram. -/
theorem unionRestriction (a : A) :
    (F.obj a).diagram = (unionEmbedding F a).hom.monotone.functor ⋙ unionDiagram F := by
  refine Functor.ext (fun i ↦ (unionObject_embedding F a i).symm) ?_
  intro i j f
  change (F.obj a).diagram.map f =
    eqToHom (unionObject_embedding F a i).symm ≫
      unionMap F ((unionEmbedding F a).hom.monotone (leOfHom f)) ≫
        eqToHom (unionObject_embedding F a j)
  rw [unionMap_embedding F a i j (leOfHom f)]
  simp only [stageMap, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, eqToHom_trans, Category.comp_id]
  congr 1

/-- The colimit cocone of compatible diagrams. -/
noncomputable def unionCocone : Cocone F where
  pt := ⟨unionIndex F, unionDiagram F⟩
  ι.app a := ⟨unionEmbedding F a, unionRestriction F a⟩
  ι.naturality _ _ f := Hom.ext (colimit.w (F ⋙ indexFunctor) f)

/-- Two functors from a union poset are equal if they agree on all stages. -/
theorem functor_ext {D : Type*} [Category* D] (G H : unionIndex F ⥤ D)
    (h : ∀ a, (unionEmbedding F a).hom.monotone.functor ⋙ G =
      (unionEmbedding F a).hom.monotone.functor ⋙ H) : G = H := by
  refine Functor.ext
    (fun i ↦ by
      obtain ⟨a, x, rfl⟩ := unionEmbedding_jointly_surjective F i
      exact Functor.congr_obj (h a) x) ?_
  intro i j f
  obtain ⟨a, x, y, rfl, rfl, hxy⟩ := union_le_rep F (leOfHom f)
  have hf : f = (unionEmbedding F a).hom.monotone.functor.map (homOfLE hxy) :=
    Subsingleton.elim _ _
  rw [hf]
  exact Functor.congr_hom (h a) (homOfLE hxy)

/-- The map of index posets from the union to another compatible cocone. -/
noncomputable def unionDescIndex (s : Cocone F) : unionIndex F ⟶ s.pt.index :=
  colimit.desc (F ⋙ indexFunctor) (indexFunctor.mapCocone s)

@[simp] theorem unionDescIndex_fac (s : Cocone F) (a : A) :
    unionEmbedding F a ≫ unionDescIndex F s = (s.ι.app a).embedding :=
  colimit.ι_desc (indexFunctor.mapCocone s) a

/-- The descended index map respects the glued diagram. -/
theorem unionDesc_restriction (s : Cocone F) :
    unionDiagram F = (unionDescIndex F s).hom.monotone.functor ⋙ s.pt.diagram := by
  apply functor_ext F
  intro a
  calc
    _ = (F.obj a).diagram := (unionRestriction F a).symm
    _ = (s.ι.app a).embedding.hom.monotone.functor ⋙ s.pt.diagram :=
      (s.ι.app a).restriction
    _ = _ := by
      have he := unionDescIndex_fac F s a
      have hh : (s.ι.app a).embedding.hom.monotone.functor =
          (unionEmbedding F a).hom.monotone.functor ⋙
            (unionDescIndex F s).hom.monotone.functor := by
        rw [← he]
        rfl
      rw [hh]
      rfl

/-- The universal map out of the union cocone. -/
noncomputable def unionDesc (s : Cocone F) : (unionCocone F).pt ⟶ s.pt :=
  ⟨unionDescIndex F s, unionDesc_restriction F s⟩

/-- Compatible systems have filtered colimits, computed by unions of the index posets. -/
noncomputable def unionIsColimit : IsColimit (unionCocone F) where
  desc := unionDesc F
  fac s a := Hom.ext (unionDescIndex_fac F s a)
  uniq s m hm := by
    apply Hom.ext
    apply colimit.hom_ext
    intro a
    exact (congrArg Hom.embedding (hm a)).trans (unionDescIndex_fac F s a).symm

instance : HasColimit F := ⟨⟨_, unionIsColimit F⟩⟩

instance : PreservesColimit F (indexFunctor.{u, v, w} (C := C)) :=
  preservesColimit_of_preserves_colimit_cocone (unionIsColimit F)
    (colimit.isColimit (F ⋙ indexFunctor))

instance : HasColimitsOfShape A (PointSystemDiagram.{u, v, w} C) where

instance : PreservesColimitsOfShape A (indexFunctor.{u, v, w} (C := C)) where
  preservesColimit {G} := preservesColimit_of_preserves_colimit_cocone (unionIsColimit G)
    (colimit.isColimit (G ⋙ indexFunctor))

instance : HasFilteredColimitsOfSize.{w, w} (PointSystemDiagram.{u, v, w} C) where
  HasColimitsOfShape _ := inferInstance

instance : PreservesFilteredColimitsOfSize.{w, w} (indexFunctor.{u, v, w} (C := C)) where
  preserves_filtered_colimits _ := inferInstance

end PointSystemDiagram

end CategoryTheory
