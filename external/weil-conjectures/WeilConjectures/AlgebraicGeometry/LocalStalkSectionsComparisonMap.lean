/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-! # The canonical degree-zero local-scheme comparison map

Source: Stacks Project, Tag 03Q6, the pullback maps in Lemma 59.51.5.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

namespace LocalStalkSections

variable {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
  (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)

/-- Identify the supplied open object with its canonical open subscheme. 
(blueprint: new-local-stalk-sections-comparison-map)
-/
noncomputable def openIso (U : X.Opens) :
    (Scheme.Etale.forget X).obj (i.obj U) ≅ X.restrictFunctor.obj U :=
  eqToIso (congrArg (fun F : X.Opens ⥤ Over X ↦ F.obj U) hi)

set_option backward.isDefEq.respectTransparency false in
/-- The local scheme maps canonically into every open neighbourhood of its point. 
(blueprint: new-local-stalk-sections-comparison-map)
-/
noncomputable def lift (U : OpenNhds x) :
    Spec (X.presheaf.stalk x) ⟶ (i.obj U.1).left :=
  Scheme.Opens.fromSpecStalkOfMem U.1 x U.property ≫ (openIso i hi U.1).inv.left

set_option backward.isDefEq.respectTransparency false in
/-- The neighbourhood lift lies over the canonical map to X.
Source: Stacks Project, Tag 03Q6, the canonical degree-zero pullback maps.
(blueprint: new-local-stalk-sections-comparison-map)

Proof: Compose the equality-induced inverse in Over X with the structure map.
Its over-category compatibility reduces the composite to the canonical map to
an open followed by its inclusion, which is Scheme.Opens.fromSpecStalkOfMem_ι. -/
lemma lift_fac (U : OpenNhds x) :
    lift i hi x U ≫ (i.obj U.1).hom = X.fromSpecStalk x := by
  have hw : (openIso i hi U.1).inv.left ≫ (i.obj U.1).hom = Scheme.Opens.ι U.1 :=
    (openIso i hi U.1).inv.w
  rw [lift, Category.assoc, hw]
  exact Scheme.Opens.fromSpecStalkOfMem_ι U.1 x U.property

include hi in
set_option backward.isDefEq.respectTransparency false in
/-- The structural map of a supplied open object is monic.
Source: Stacks Project, Tag 03Q6, identifying neighbourhoods with open subschemes.
(blueprint: new-local-stalk-sections-comparison-map)

Proof: The equality-induced over-category isomorphism identifies the structural
map with an isomorphism followed by the canonical open inclusion. Both are open
immersions, and every open immersion is monic. -/
lemma open_mono (U : X.Opens) : Mono (i.obj U).hom := by
  let e := openIso i hi U
  have he : IsIso e.hom.left := inferInstance
  have ho : IsOpenImmersion (i.obj U).hom := by
    have hw : e.hom.left ≫ U.ι = (i.obj U).hom := e.hom.w
    rw [← hw]
    infer_instance
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Neighbourhood lifts commute with inclusions.
Source: Stacks Project, Tag 03Q6, compatibility of degree-zero pullback maps.
(blueprint: new-local-stalk-sections-comparison-map)

Proof: Postcompose both lifts with the larger neighbourhood's monic structural
map. The over-category relation and lift_fac identify both composites with
X.fromSpecStalk x. Cancel the monomorphism. -/
lemma lift_naturality {U V : OpenNhds x} (f : U ⟶ V) :
    lift i hi x U ≫ (i.map ((OpenNhds.inclusion x).map f)).left = lift i hi x V := by
  have := open_mono i hi V.1
  apply (cancel_mono (i.obj V.1).hom).1
  have hw : (i.map ((OpenNhds.inclusion x).map f)).left ≫ (i.obj V.1).hom =
      (i.obj U.1).hom := MorphismProperty.Over.w _
  rw [Category.assoc, hw]
  exact (lift_fac i hi x U).trans (lift_fac i hi x V).symm

set_option backward.isDefEq.respectTransparency false in
/-- A neighbourhood becomes a pointed etale object after base change to the local scheme. 
(blueprint: new-local-stalk-sections-comparison-map)
-/
noncomputable def baseChangeSection (U : OpenNhds x) :
    Scheme.Etale.mk (𝟙 (Spec (X.presheaf.stalk x))) ⟶
      (X.fromSpecStalk x).Etale.obj (i.obj U.1) :=
  MorphismProperty.Over.homMk
    (pullback.lift (lift i hi x U) (𝟙 _) (by simpa using lift_fac i hi x U))
    (by exact pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The terminal-to-base-change sections commute with neighbourhood inclusions.
Source: Stacks Project, Tag 03Q6, compatibility of degree-zero pullback maps.
(blueprint: new-local-stalk-sections-comparison-map)

Proof: Compare the underlying scheme maps by the two pullback projections.
The first projection is lift_naturality, and the second is the identity.
The pullback universal property and faithfulness to schemes give equality. -/
lemma section_naturality {U V : OpenNhds x} (f : U ⟶ V) :
    baseChangeSection i hi x U ≫ (X.fromSpecStalk x).Etale.map
      (i.map ((OpenNhds.inclusion x).map f)) = baseChangeSection i hi x V := by
  apply MorphismProperty.Over.Hom.ext
  change (baseChangeSection i hi x U).left ≫
    ((X.fromSpecStalk x).Etale.map (i.map ((OpenNhds.inclusion x).map f))).left =
      (baseChangeSection i hi x V).left
  apply pullback.hom_ext
  · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst]
    change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ =
      pullback.lift _ _ _ ≫ pullback.fst _ _
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
    exact lift_naturality i hi x f
  · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd]
    change pullback.lift _ _ _ ≫ pullback.snd _ _ =
      pullback.lift _ _ _ ≫ pullback.snd _ _
    simp only [pullback.lift_snd]

variable (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
  (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} X.smallEtaleTopology
    (Spec (X.presheaf.stalk x)).smallEtaleTopology)

/-- The diagram defining the Zariski stalk of sections of an etale sheaf. 
(blueprint: new-local-stalk-sections-comparison-map)
-/
abbrev neighbourhoodDiagram (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ((OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x) ⋙ i).op ⋙ F.obj

set_option backward.isDefEq.respectTransparency false in
/-- Pull back a neighbourhood section by the adjunction unit, then by its local-scheme section. 
(blueprint: new-local-stalk-sections-comparison-map)
-/
noncomputable def cocone (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Cocone (neighbourhoodDiagram i x F) where
  pt := (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 _)))
  ι :=
    { app := fun U ↦ (hH.unit.app F).hom.app (op (i.obj U.unop.1)) ≫
        (H.obj F).obj.map (baseChangeSection i hi x U.unop).op
      naturality := by
        intro U V f
        dsimp only [neighbourhoodDiagram, Functor.comp_map, Functor.op_map,
          Functor.const_obj_obj, Functor.const_obj_map]
        have hu : F.obj.map (i.map ((OpenNhds.inclusion x).map f.unop)).op ≫
            (hH.unit.app F).hom.app (op (i.obj V.unop.1)) =
            (hH.unit.app F).hom.app (op (i.obj U.unop.1)) ≫
              (H.obj F).obj.map
                ((X.fromSpecStalk x).Etale.map (i.map ((OpenNhds.inclusion x).map f.unop))).op :=
          (hH.unit.app F).hom.naturality _
        rw [Category.comp_id, ← Category.assoc, hu, Category.assoc, ← Functor.map_comp]
        congr 1
        exact congrArg (fun g ↦ (H.obj F).obj.map g.op)
          (section_naturality i hi x f.unop) }

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from neighbourhood germs to sections on the local scheme.
It is induced by the adjunction unit and the canonical local-scheme maps to neighbourhoods.
Source: Stacks Project, Tag 03Q6, the degree-zero pullback map of Lemma 59.51.5.
(blueprint: new-local-stalk-sections-comparison-map) -/
noncomputable def comparison :
    etaleObjectStalkSections X i x ⟶
      H ⋙ (sheafSections (Spec (X.presheaf.stalk x)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 _))) where
  app F := colimit.desc (neighbourhoodDiagram i x F) (cocone i hi x H hH F)
  naturality := by
    intro F G f
    apply colimit.hom_ext
    intro U
    dsimp only [etaleObjectStalkSections, Functor.comp_map]
    rw [colimit.ι_map_assoc]
    change f.hom.app (op (i.obj U.unop.1)) ≫
      colimit.ι (neighbourhoodDiagram i x G) U ≫
        colimit.desc (neighbourhoodDiagram i x G) (cocone i hi x H hH G) =
      (colimit.ι (neighbourhoodDiagram i x F) U ≫
        colimit.desc (neighbourhoodDiagram i x F) (cocone i hi x H hH F)) ≫
          (H.map f).hom.app (op (Scheme.Etale.mk (𝟙 _)))
    rw [colimit.ι_desc, colimit.ι_desc]
    dsimp only [cocone]
    have hu : f.hom.app (op (i.obj U.unop.1)) ≫
        (hH.unit.app G).hom.app (op (i.obj U.unop.1)) =
        (hH.unit.app F).hom.app (op (i.obj U.unop.1)) ≫
          (H.map f).hom.app (op ((X.fromSpecStalk x).Etale.obj (i.obj U.unop.1))) :=
      congrArg (fun g ↦ g.hom.app (op (i.obj U.unop.1))) (hH.unit.naturality f)
    have hn := (H.map f).hom.naturality (baseChangeSection i hi x U.unop).op
    rw [← Category.assoc, hu, Category.assoc, ← hn, ← Category.assoc]

/-- The comparison sends each neighbourhood section to its unit pullback.
Source: Stacks Project, Tag 03Q6, the defining degree-zero pullback map.
(blueprint: new-local-stalk-sections-comparison-map) -/
@[reassoc]
theorem ι_comparison (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : (OpenNhds x)ᵒᵖ) :
    colimit.ι (neighbourhoodDiagram i x F) U ≫ (comparison i hi x H hH).app F =
      (cocone i hi x H hH F).ι.app U :=
  colimit.ι_desc _ _

end LocalStalkSections
