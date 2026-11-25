/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
/-! # The sheaf approximation diagram of a scheme cone

For a cone with projections `pᵢ`, construct the diagram `pᵢ⁻¹pᵢ*F` and its
counit cocone to `F`. The transition maps are defined by adjunction; their
functoriality follows from coherence of direct-image composition.

Source: the first step of blueprint `lemma-uniform-bounds-pro-etale-affines`.
(blueprint: def-sc-affine-limit-sheaf-approximation). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale.AffineLimitSheafApproximation
variable {X Y Z W : Scheme.{u}}
local notation "L" => upperStar AddCommGrpCat
local notation "R" => lowerStar AddCommGrpCat
local notation "adj" => upperStarLowerStarAdjunction AddCommGrpCat

/-- Transition morphism between two pull-push approximations.
Source: blueprint `lemma-uniform-bounds-pro-etale-affines`, proof step 1.
(blueprint: def-sc-affine-limit-sheaf-approximation). -/
noncomputable def approximationMap (p : X ⟶ Y) (f : Y ⟶ Z) (r : X ⟶ Z)
    (hr : r = p ≫ f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (L r).obj ((R r).obj F) ⟶ (L p).obj ((R p).obj F) :=
  ((adj r).homEquiv _ _).symm
    ((lowerStarComp AddCommGrpCat.{u + 1} p f r hr).inv.app F ≫
      (R f).map ((adj p).unit.app ((R p).obj F)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} p f r hr).hom.app ((L p).obj ((R p).obj F)))

lemma approximationMap_transpose (p : X ⟶ Y) (f : Y ⟶ Z) (r : X ⟶ Z)
    (hr : r = p ≫ f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (adj r).unit.app ((R r).obj F) ≫ (R r).map (approximationMap p f r hr F) =
      (lowerStarComp AddCommGrpCat.{u + 1} p f r hr).inv.app F ≫
        (R f).map ((adj p).unit.app ((R p).obj F)) ≫
        (lowerStarComp AddCommGrpCat.{u + 1} p f r hr).hom.app ((L p).obj ((R p).obj F)) := by
  exact ((adj r).homEquiv _ _).apply_symm_apply _

lemma approximationMap_counit (p : X ⟶ Y) (f : Y ⟶ Z) (r : X ⟶ Z)
    (hr : r = p ≫ f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    approximationMap p f r hr F ≫ (adj p).counit.app F = (adj r).counit.app F := by
  apply ((adj r).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [show ((adj r).homEquiv _ _) (approximationMap p f r hr F) = _ from
    ((adj r).homEquiv _ _).apply_symm_apply _]
  rw [Category.assoc, Category.assoc, ← NatTrans.naturality]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc ((lowerStarComp AddCommGrpCat.{u + 1} p f r hr).inv.app F),
    ← Functor.map_comp]
  simp [Adjunction.homEquiv_unit]

lemma approximationMap_id (p : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    approximationMap p (𝟙 Y) p (Category.comp_id p).symm F = 𝟙 _ := by
  apply ((adj p).homEquiv _ _).injective
  change ((adj p).homEquiv _ _) (((adj p).homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  rw [lowerStarComp_id_right]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp]
  rw [← NatTrans.naturality_assoc]
  simp [Adjunction.homEquiv_unit]

lemma approximationMap_comp (p : X ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ W)
    (r : X ⟶ Z) (t : X ⟶ W) (hr : r = p ≫ f) (ht : t = r ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    approximationMap r g t ht F ≫ approximationMap p f r hr F =
      approximationMap p (f ≫ g) t (by rw [ht, hr, Category.assoc]) F := by
  apply ((adj t).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [show ((adj t).homEquiv _ _) (approximationMap r g t ht F) = _ from
    ((adj t).homEquiv _ _).apply_symm_apply _]
  rw [show ((adj t).homEquiv _ _)
      (approximationMap p (f ≫ g) t _ F) = _ from
    ((adj t).homEquiv _ _).apply_symm_apply _]
  rw [Category.assoc, Category.assoc, ← NatTrans.naturality]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc ((lowerStarComp AddCommGrpCat.{u + 1} r g t ht).inv.app F), ← Functor.map_comp,
    approximationMap_transpose]
  simp only [Functor.map_comp, Category.assoc]
  have he : Functor.isoWhiskerRight (lowerStarComp AddCommGrpCat.{u + 1} p f r hr) (R g) ≪≫
      lowerStarComp AddCommGrpCat.{u + 1} r g t ht =
      Functor.isoWhiskerLeft (R p) (lowerStarComp AddCommGrpCat.{u + 1} f g (f ≫ g) rfl) ≪≫
        lowerStarComp AddCommGrpCat.{u + 1} p (f ≫ g) t (by rw [ht, hr, Category.assoc]) := by
    apply Iso.ext
    exact lowerStarComp_assoc' AddCommGrpCat.{u + 1} p f g r (f ≫ g) t hr rfl ht
  have heh := congrArg (fun e ↦ e.hom.app ((L p).obj ((R p).obj F))) he
  have hei := congrArg (fun e ↦ e.inv.app F) he
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at heh
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app] at hei
  rw [heh, ← Category.assoc, ← Category.assoc, hei]
  simp only [Category.assoc]
  have hn := (lowerStarComp AddCommGrpCat.{u + 1} f g (f ≫ g) rfl).inv.naturality
    ((adj p).unit.app ((R p).obj F))
  change (R (f ≫ g)).map _ ≫ _ = _ ≫ (R g).map ((R f).map _) at hn
  rw [← reassoc_of% hn]
  simp

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (s : Cone D)
    (F : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- The diagram of pull-push approximations along the projections of a scheme cone.
Source: blueprint `lemma-uniform-bounds-pro-etale-affines`, proof step 1.
(blueprint: def-sc-affine-limit-sheaf-approximation). -/
noncomputable def approximationDiagram :
    Iᵒᵖ ⥤ Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj i := (L (s.π.app i.unop)).obj ((R (s.π.app i.unop)).obj F)
  map {i j} f := approximationMap (s.π.app j.unop) (D.map f.unop)
    (s.π.app i.unop) (s.w f.unop).symm F
  map_id i := by
    simpa only [unop_id, D.map_id] using approximationMap_id (s.π.app i.unop) F
  map_comp {i j k} f g := by
    simpa only [unop_comp, D.map_comp] using
      (approximationMap_comp (s.π.app k.unop) (D.map g.unop) (D.map f.unop)
        (s.π.app j.unop) (s.π.app i.unop) (s.w g.unop).symm (s.w f.unop).symm F).symm

set_option backward.isDefEq.respectTransparency false in
/-- The counits form a cocone from the approximation diagram to the original sheaf.
Source: blueprint `lemma-uniform-bounds-pro-etale-affines`, proof step 1.
(blueprint: def-sc-affine-limit-sheaf-approximation). -/
noncomputable def approximationCocone : Cocone (approximationDiagram D s F) where
  pt := F
  ι :=
    { app := fun i ↦ (adj (s.π.app i.unop)).counit.app F
      naturality := fun i j f ↦ by
        dsimp only [approximationDiagram, Functor.const_obj_map]
        exact (approximationMap_counit _ _ _ _ _).trans (Category.comp_id _).symm }

/-- The canonical map from the colimit of approximations to the original sheaf.
Source: blueprint `lemma-uniform-bounds-pro-etale-affines`, proof step 1.
(blueprint: def-sc-affine-limit-sheaf-approximation). -/
noncomputable def approximationComparison :
    colimit (approximationDiagram D s F) ⟶ F :=
  colimit.desc (approximationDiagram D s F) (approximationCocone D s F)

end AlgebraicGeometry.Etale.AffineLimitSheafApproximation
