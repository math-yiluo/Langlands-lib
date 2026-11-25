/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleSectionSystem
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
/-! # Functoriality of canonical section comparisons -/
@[expose] public section
universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical section comparisons compose, with arbitrary Grothendieck coefficients. -/
theorem Etale.grothendieckRelativeSectionMap_comp {R S T W : Scheme.{u}}
    (h : T ⟶ S) (g : W ⟶ T) (f : S ⟶ R) (k : T ⟶ R) (l : W ⟶ R)
    (hk : h ≫ f = k) (hl : g ≫ k = l) (F : Sheaf R.smallEtaleTopology A) :
    Etale.grothendieckRelativeSectionMap A h f k hk F ≫
        Etale.grothendieckRelativeSectionMap A g k l hl F =
      Etale.grothendieckRelativeSectionMap A (g ≫ h) f l (by rw [Category.assoc, hk, hl]) F := by
  subst k
  subst l
  ext U
  let B := f.Etale.obj U.unop
  let C := h.Etale.obj B
  let E := (h ≫ f).Etale.obj U.unop
  let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom
  have hn := ((Etale.upperStarLowerStarAdjunction A g).unit.app
    ((Etale.upperStar A (h ≫ f)).obj F)).hom.naturality (p.app U.unop).op
  have hs := NatTrans.congr_app (congrArg (fun e ↦ e.hom)
    ((Etale.upperStarLowerStarAdjunction A g).unit.naturality
      ((Etale.upperStarComp A h f).inv.app F))) (op C)
  have hc := NatTrans.congr_app (congrArg (fun e ↦ e.hom)
    (NatTrans.congr_app (congrArg Iso.inv (Etale.upperStarComp_assoc A g h f)) F))
      (op (g.Etale.obj C))
  have hn' := (((Etale.upperStarComp A g (h ≫ f)).inv.app F).hom.naturality
    (g.Etale.map (p.app U.unop)).op)
  change ((Etale.upperStar A (h ≫ f)).obj F).obj.map (p.app U.unop).op ≫
      ((Etale.upperStarLowerStarAdjunction A g).unit.app
        ((Etale.upperStar A (h ≫ f)).obj F)).hom.app (op E) =
    ((Etale.upperStarLowerStarAdjunction A g).unit.app
      ((Etale.upperStar A (h ≫ f)).obj F)).hom.app (op C) ≫
      ((Etale.upperStar A g).obj ((Etale.upperStar A (h ≫ f)).obj F)).obj.map
        (g.Etale.map (p.app U.unop)).op at hn
  change ((Etale.upperStarComp A h f).inv.app F).hom.app (op C) ≫
      ((Etale.upperStarLowerStarAdjunction A g).unit.app
        ((Etale.upperStar A (h ≫ f)).obj F)).hom.app (op C) =
    ((Etale.upperStarLowerStarAdjunction A g).unit.app
      ((Etale.upperStar A h).obj ((Etale.upperStar A f).obj F))).hom.app (op C) ≫
      ((Etale.upperStar A g).map ((Etale.upperStarComp A h f).inv.app F)).hom.app
        (op (g.Etale.obj C)) at hs
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.associator_inv_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Category.id_comp] at hc
  simp only [Etale.grothendieckRelativeSectionMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.op_app]
  simp only [Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hs, reassoc_of% hn', reassoc_of% hc]
  dsimp only [B, C, E, Functor.op_obj, Functor.comp_obj, Etale.grothendieckRelativeSections] at *
  erw [reassoc_of% (Etale.section_unit_comp A h g ((Etale.upperStar A f).obj F) B)]
  have ht := (((Etale.upperStarComp A (g ≫ h) f (g ≫ h ≫ f)
    (Category.assoc g h f).symm).inv.app F).hom.naturality
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app B).op)
  erw [reassoc_of% ht]
  simp only [← Functor.map_comp, ← op_comp]
  have hp := congrArg (fun e ↦ e.hom.app U.unop)
    (MorphismProperty.Over.pullbackComp_assoc (P := @Etale) (Q := ⊤) g h f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at hp
  dsimp only [p] at ⊢
  dsimp only [Scheme.Hom.Etale, B] at *
  erw [hp]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison for the identity morphism is the identity. -/
theorem Etale.grothendieckRelativeSectionMap_id {R S : Scheme.{u}} (f : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A) :
    Etale.grothendieckRelativeSectionMap A (𝟙 S) f f (Category.id_comp f) F = 𝟙 _ := by
  let a := Etale.grothendieckRelativeSectionMap A (𝟙 S) f f (Category.id_comp f) F
  have : ∀ U, IsIso (a.app U) := by
    intro U
    dsimp only [a, Etale.grothendieckRelativeSectionMap, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.op_app]
    infer_instance
  have : IsIso a := NatIso.isIso_of_isIso_app a
  have ha := Etale.grothendieckRelativeSectionMap_comp A (𝟙 S) (𝟙 S) f f f
    (Category.id_comp f) (Category.id_comp f) F
  simp only [Category.id_comp] at ha
  apply (cancel_epi a).1
  simpa only [Category.comp_id] using ha

/-- The actual presheaf section system over the category of stages mapping to i.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2.
For composition, move the first pullback-pasting restriction across the second unit by presheaf
naturality, then move the first coefficient composition isomorphism across that unit by sheaf
naturality. Inverse-image associativity combines the two coefficient isomorphisms. The
composite-unit equation combines the units, and pullback-pasting associativity cancels the
remaining inverse pasting map. For identity, the unit for an identity scheme map and all other
comparison factors are isomorphisms. Composition makes this map idempotent; cancel it to get
identity. These laws give the diagram functor laws. Their composition formula and the cone
equation give naturality of the cocone.
(auxiliary; not a blueprint node) -/
noncomputable def Etale.relativeSectionDiagram
    {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (i : I)
    (F : Sheaf (D.obj i).smallEtaleTopology A) :
    (Over i)ᵒᵖ ⥤ ((D.obj i).Etaleᵒᵖ ⥤ A) where
  obj j := Etale.grothendieckRelativeSections A (D.map j.unop.hom) F
  map {j k} a := Etale.grothendieckRelativeSectionMap A (D.map a.unop.left) (D.map j.unop.hom)
    (D.map k.unop.hom)
    ((D.map_comp a.unop.left j.unop.hom).symm.trans
      (congrArg D.map a.unop.w)) F
  map_id j := by
    simp only [unop_id, Over.id_left, D.map_id]
    exact Etale.grothendieckRelativeSectionMap_id A _ F
  map_comp {j k l} a b := by
    dsimp only [unop_comp, Over.comp_left]
    rw [Etale.grothendieckRelativeSectionMap_comp]
    congr 1
    exact D.map_comp _ _

/-- The unit section comparisons along a cone form a canonical cocone. -/
noncomputable def Etale.relativeSectionCocone
    {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (F : Sheaf (D.obj i).smallEtaleTopology A) :
    Cocone (Etale.relativeSectionDiagram A D i F) where
  pt := Etale.grothendieckRelativeSections A (c.π.app i) F
  ι :=
    { app := fun j ↦ Etale.grothendieckRelativeSectionMap A (c.π.app j.unop.left)
        (D.map j.unop.hom) (c.π.app i) (c.w j.unop.hom) F
      naturality := by
        intro j k a
        dsimp only [Etale.relativeSectionDiagram, Functor.const_obj_map]
        rw [Etale.grothendieckRelativeSectionMap_comp]
        erw [Category.comp_id]
        congr 1
        exact c.w a.unop.left }

end AlgebraicGeometry
