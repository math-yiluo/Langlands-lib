/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PointSystemDiagram
public import WeilConjectures.CategoryTheory.PointSystemChain
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.Order.Hom.Set
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Pointed systems and their directed unions

Source: Stacks Project, Sites, Tag 00YP (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w t

open CategoryTheory Limits

namespace CategoryTheory.PointSystemDiagram

attribute [local instance] IsFiltered.isConnected

variable {C : Type u} [Category.{v} C]

/-- The map induced on presheaf colimits by a strict refinement. -/
noncomputable def Hom.colimitMap {X Y : PointSystemDiagram.{u, v, w} Cᵒᵖ}
    (f : X ⟶ Y) (P : Cᵒᵖ ⥤ Type (max w t)) :
    colimit (X.diagram ⋙ P) ⟶ colimit (Y.diagram ⋙ P) :=
  pointSystemRefinementMapOfPreorder X.diagram Y.diagram f.embedding.hom f.restriction P

@[simp] theorem Hom.colimitMap_comp {X Y Z : PointSystemDiagram.{u, v, w} Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (P : Cᵒᵖ ⥤ Type (max w t)) :
    (f ≫ g).colimitMap P = f.colimitMap P ≫ g.colimitMap P :=
  (pointSystemRefinementMapOfPreorder_comp _ _ _ _ _ _ _ P).symm

@[simp] theorem Hom.colimitMap_id (X : PointSystemDiagram.{u, v, w} Cᵒᵖ)
    (P : Cᵒᵖ ⥤ Type (max w t)) : (𝟙 X : X ⟶ X).colimitMap P = 𝟙 _ := by
  apply colimit.hom_ext
  intro j
  change colimit.ι (X.diagram ⋙ P) j ≫
    pointSystemRefinementMapOfPreorder _ _ _ _ P = _
  rw [pointSystemRefinementMapOfPreorder_ι]
  simp
  rfl

variable (X : PointSystemDiagram.{u, v, w} Cᵒᵖ)

/-- The original diagram is part of the data of a pointed refinement. -/
abbrev Extension := Under X

namespace Extension

variable {X}

abbrev embedding (Y : Extension X) : X.index ↪o Y.right.index := Y.hom.embedding.hom

abbrev restriction (Y : Extension X) :
    X.diagram = Y.embedding.monotone.functor ⋙ Y.right.diagram := Y.hom.restriction

/-- The canonical map from the original system to an extension. -/
noncomputable abbrev map (Y : Extension X) (P : Cᵒᵖ ⥤ Type (max w t)) :=
  Y.hom.colimitMap P

@[simp] theorem map_comp {Y Z : Extension X} (f : Y ⟶ Z)
    (P : Cᵒᵖ ⥤ Type (max w t)) :
    Y.map P ≫ f.right.colimitMap P = Z.map P := by
  rw [← Hom.colimitMap_comp, Under.w f]

@[simp] theorem embedding_comp {Y Z : Extension X} (f : Y ⟶ Z) (j : X.index) :
    f.right.embedding (Y.embedding j) = Z.embedding j := by
  exact congrArg (fun h : X ⟶ Z.right ↦ h.embedding j) (Under.w f)

variable {A : Type w} [PartialOrder A] [Nonempty A] [IsDirectedOrder A]
    (F : A ⥤ Extension X) (c : Cocone F)

/-- Ranges of the stage embeddings present a cocone as a nested chain. -/
noncomputable def chain
    (hjoint : ∀ i : c.pt.right.index,
      ∃ (a : A) (j : (F.obj a).right.index), (c.ι.app a).right.embedding j = i)
    (hnonempty : ∀ a, Nonempty (F.obj a).right.index)
    (hdir : ∀ a, IsDirectedOrder (F.obj a).right.index) : PointSystemChain X.diagram where
  Index := c.pt.right.index
  indexOrder := inferInstance
  Stage := A
  stageOrder := inferInstance
  stageNonempty := inferInstance
  stageDirected := inferInstance
  diagram := c.pt.right.diagram
  embedding := c.pt.embedding
  restriction := c.pt.restriction
  stage a := Set.range (c.ι.app a).right.embedding
  stage_mono a b hab := by
    rintro i ⟨j, rfl⟩
    refine ⟨(F.map (homOfLE hab)).right.embedding j, ?_⟩
    exact congrArg (fun h : F.obj a ⟶ c.pt ↦ h.right.embedding j) (c.w (homOfLE hab))
  stage_nonempty a := by
    have := hnonempty a
    exact Set.range_nonempty _
  stage_directed a := by
    have := hdir a
    rintro i ⟨j, rfl⟩ i' ⟨j', rfl⟩
    obtain ⟨k, hj, hj'⟩ := exists_ge_ge j j'
    exact ⟨_, ⟨k, rfl⟩, (c.ι.app a).right.embedding.hom.monotone hj,
      (c.ι.app a).right.embedding.hom.monotone hj'⟩
  exhaustive i := by simpa only [Set.mem_range] using hjoint i
  original_mem a j := ⟨(F.obj a).embedding j, embedding_comp (c.ι.app a) j⟩

/-- A stage is isomorphic, as an index poset, to its range in the union. -/
noncomputable def rangeIso (a : A) : (F.obj a).right.index ≃o
    Set.range (c.ι.app a).right.embedding.hom := OrderEmbedding.orderIso

/-- The original index embeds into the inverse of the range parametrization. -/
theorem stageEmbedding_rangeIso
    (hj hn hd) (a : A) :
    ((chain F c hj hn hd).stageEmbedding a).trans
      (rangeIso F c a).symm.toOrderEmbedding = (F.obj a).embedding := by
  ext j
  apply (c.ι.app a).right.embedding.hom.injective
  exact (congrArg Subtype.val ((rangeIso F c a).apply_symm_apply
    ((chain F c hj hn hd).stageEmbedding a j))).trans
      (embedding_comp (c.ι.app a) j).symm

/-- The range diagram recovers the original stage after inverse parametrization. -/
theorem stageDiagram_rangeIso (hj hn hd) (a : A) :
    (chain F c hj hn hd).stageDiagram a =
      (rangeIso F c a).symm.monotone.functor ⋙ (F.obj a).right.diagram := by
  rw [(c.ι.app a).right.restriction]
  refine Functor.ext (fun j ↦ ?_) ?_
  · exact congrArg c.pt.right.diagram.obj
      (congrArg Subtype.val ((rangeIso F c a).apply_symm_apply j)).symm
  · intro i j f
    have hi : (c.ι.app a).right.embedding ((rangeIso F c a).symm i) = i.val :=
      congrArg Subtype.val ((rangeIso F c a).apply_symm_apply i)
    have hj' : (c.ι.app a).right.embedding ((rangeIso F c a).symm j) = j.val :=
      congrArg Subtype.val ((rangeIso F c a).apply_symm_apply j)
    change c.pt.right.diagram.map _ =
      eqToHom (congrArg c.pt.right.diagram.obj hi.symm) ≫
      c.pt.right.diagram.map _ ≫ eqToHom (congrArg c.pt.right.diagram.obj hj')
    rw [← eqToHom_map _ hi.symm, ← eqToHom_map _ hj',
      ← Functor.map_comp_assoc, ← Functor.map_comp]
    congr 1

/-- Separation of the two original classes passes to the range stage. -/
theorem chain_stage_ne [Nonempty X.index] [IsDirectedOrder X.index]
    (hj hn hd) (P : Cᵒᵖ ⥤ Type (max w t)) (s s' : colimit (X.diagram ⋙ P))
    (hne : ∀ a, (F.obj a).map P s ≠ (F.obj a).map P s') (a : A) :
    pointSystemRefinementMapOfPreorder X.diagram ((chain F c hj hn hd).stageDiagram a)
      ((chain F c hj hn hd).stageEmbedding a)
      ((chain F c hj hn hd).stageRestriction a) P s ≠
    pointSystemRefinementMapOfPreorder X.diagram ((chain F c hj hn hd).stageDiagram a)
      ((chain F c hj hn hd).stageEmbedding a)
      ((chain F c hj hn hd).stageRestriction a) P s' := by
  intro heq
  have hh := ConcreteCategory.congr_hom (pointSystemRefinementMapOfPreorder_comp X.diagram
    ((chain F c hj hn hd).stageDiagram a) (F.obj a).right.diagram
    ((chain F c hj hn hd).stageEmbedding a) (rangeIso F c a).symm.toOrderEmbedding
    ((chain F c hj hn hd).stageRestriction a) (stageDiagram_rangeIso F c hj hn hd a) P) s
  have hh' := ConcreteCategory.congr_hom (pointSystemRefinementMapOfPreorder_comp X.diagram
    ((chain F c hj hn hd).stageDiagram a) (F.obj a).right.diagram
    ((chain F c hj hn hd).stageEmbedding a) (rangeIso F c a).symm.toOrderEmbedding
    ((chain F c hj hn hd).stageRestriction a) (stageDiagram_rangeIso F c hj hn hd a) P) s'
  simp only [stageEmbedding_rangeIso F c hj hn hd a] at hh hh'
  exact hne a (hh.symm.trans
    ((congrArg (pointSystemRefinementMapOfPreorder _ _ _ _ P) heq).trans hh'))

/-- A colimit cocone has jointly surjective index embeddings. -/
theorem index_jointly_surjective (hc : IsColimit c) (i : c.pt.right.index) :
    ∃ (a : A) (j : (F.obj a).right.index), (c.ι.app a).right.embedding j = i :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (Under.forget X ⋙ indexFunctor.{u, v, w} ⋙ forget PartOrdEmb) hc) i

variable [Nonempty X.index] [IsDirectedOrder X.index]
    (P : Cᵒᵖ ⥤ Type (max w t)) (s s' : colimit (X.diagram ⋙ P))

/-- Good pointed systems are directed and keep the specified two classes distinct. -/
def Good : ObjectProperty (Extension X) := fun Y ↦
  Nonempty Y.right.index ∧ IsDirectedOrder Y.right.index ∧ Y.map P s ≠ Y.map P s'

/-- Directed unions of good systems are good.
Source: Stacks Project, Sites, Tag 00YP, conditions (1) and (2) for unions
(auxiliary; not a blueprint node). -/
theorem good_of_isColimit (hc : IsColimit c) (hF : ∀ a, Good P s s' (F.obj a)) :
    Good P s s' c.pt := by
  let hj := index_jointly_surjective F c hc
  let hn := fun a ↦ (hF a).1
  let hd := fun a ↦ (hF a).2.1
  let d := chain F c hj hn hd
  refine ⟨inferInstanceAs (Nonempty d.Index), inferInstanceAs (IsDirectedOrder d.Index), ?_⟩
  exact d.ne_of_stage_ne P s s' (chain_stage_ne F c hj hn hd P s s' fun a ↦ (hF a).2.2)

variable (X)

/-- The category of good extensions of the original system. -/
abbrev GoodExtension := (Good P s s').FullSubcategory

namespace GoodExtension

variable {X P s s'}
    (F : A ⥤ GoodExtension X P s s')


/-- The union of a diagram of good extensions. -/
noncomputable def cocone : Cocone F where
  pt := ⟨colimit (F ⋙ (Good P s s').ι),
    good_of_isColimit _ _ P s s' (colimit.isColimit _) (fun a ↦ (F.obj a).property)⟩
  ι.app a := ObjectProperty.homMk (colimit.ι (F ⋙ (Good P s s').ι) a)
  ι.naturality a b f := by
    apply ObjectProperty.hom_ext
    exact colimit.w (F ⋙ (Good P s s').ι) f

/-- The union satisfies the colimit universal property. -/
noncomputable def isColimit : IsColimit (cocone F) where
  desc c := ObjectProperty.homMk (colimit.desc _ ((Good P s s').ι.mapCocone c))
  fac c a := by
    apply ObjectProperty.hom_ext
    exact colimit.ι_desc _ a
  uniq c m hm := by
    apply ObjectProperty.hom_ext
    apply colimit.hom_ext
    intro a
    exact (congrArg (fun f ↦ f.hom) (hm a)).trans
      (colimit.ι_desc ((Good P s s').ι.mapCocone c) a).symm

instance : HasColimit F := ⟨⟨_, isColimit F⟩⟩

instance : HasColimitsOfShape A (GoodExtension X P s s') where

end GoodExtension
end Extension
end CategoryTheory.PointSystemDiagram
