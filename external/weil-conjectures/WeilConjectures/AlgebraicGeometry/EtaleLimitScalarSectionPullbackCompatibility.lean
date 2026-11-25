/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Naturality of scalar inverse-image section maps

Source: Stacks Project, Sites Tags 03CB and 03CC, and Etale Cohomology Tag 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem section_unit_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hh : h = f ≫ g)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (T : Z.Etale) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app F).hom.app (op T) ≫
      ((upperStarComp AddCommGrpCat.{u + 1} f g h hh).hom.app F).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj T)) =
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F).hom.app (op T) ≫
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((upperStar AddCommGrpCat.{u + 1} g).obj F)).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj T)) ≫
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj F)).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g h hh).hom.app T).op := by
  have H := upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} f g F h hh
  have H' := congrArg (fun t ↦ t.hom.app (op T)) H
  simpa only [Adjunction.comp_unit_app, lowerStarComp,
    lowerStar_map_hom_app, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Category.assoc, Iso.symm_inv,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] using H'

/-- The normalized unit sections commute with the prescribed sheaf transitions.
Source: Stacks Project, Sites Tags 03CB and 03CC, adjunction unit naturality
and composition, used in the degree-zero proof of Etale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-pullback-compatibility).

Proof: Cancel the comparison isomorphisms eG on both sides and substitute hG.
Naturality moves the transition morphism phi across the projection unit.
The unit form of upperStarComp identifies the two successive units with the
unit for their composite, followed by the pullback composition comparison.
Evaluate this equation at Tj j. Naturality of the section restrictions moves
these comparisons across gamma and delta. Both resulting maps from the
iterated pullback to Tlim have the same first projection by the hypotheses;
they have the same second projection by their equations over the base and
cone naturality. Pullback uniqueness identifies them. This gives the stated
commuting square after restoring eG. No limit, compactness, filteredness or
sheaf colimit assertion is used. Empty objects and zero coefficients obey the
same morphism equations. -/
theorem etale_limit_scalar_section_pullback_compatibility
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale)
    :
    let J := {j : I // i₀ ≤ j}
    let Tj := fun j : J ↦
      (MorphismProperty.Over.pullback @Etale ⊤
        (D.map (homOfLE j.property).op)).obj T₀
    let Tlim := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
    ∀ (γ : ∀ (j k : J) (a : j ⟶ k),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j) ≅ Tj k)
      (δ : ∀ j : J,
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j.val))).obj (Tj j) ≅ Tlim),
      (∀ (j k : J) (a : j ⟶ k),
        (γ j k a).hom.left ≫ pullback.fst T₀.hom (D.map (homOfLE k.property).op) =
          pullback.fst (Tj j).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
      (∀ j : J,
        (δ j).hom.left ≫ pullback.fst T₀.hom (c.π.app (op i₀)) =
          pullback.fst (Tj j).hom (c.π.app (op j.val)) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
    let ρ := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (φ (show j.val ⟶ k.val from a)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j))) ≫
        (F k.val).obj.map (γ j k a).inv.op
    let ν := fun j : J ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (eG j.val).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        (G.obj j.val).obj.map (δ j).inv.op
    ∀ (j k : J) (a : j ⟶ k),
      ν j ≫ (G.map (show j.val ⟶ k.val from a)).hom.app (op Tlim) =
        ρ j k a ≫ ν k := by
  dsimp only
  intro γ δ hγ hδ j k a
  -- Normalize the transitions and cancel the comparison at j.
  rw [hG]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]
  simp only [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.inv_hom_id_assoc]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [← NatTrans.naturality_assoc]
  rw [((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k.val))
    (D.map (show j.val ⟶ k.val from a).op) (c.π.app (op j.val))
    (c.w (show j.val ⟶ k.val from a).op).symm).hom.app (F j.val)).hom.naturality_assoc
    (δ j).inv.op]
  -- Replace the unit of the composite by the two successive units.
  rw [section_unit_comp_assoc]
  have hn := congrArg (fun t ↦ t.hom.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤
      (D.map (homOfLE k.property).op)).obj T₀)))
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (c.π.app (op k.val))).unit_naturality (φ (show j.val ⟶ k.val from a)))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app] at hn
  rw [← reassoc_of% hn]
  erw [((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (c.π.app (op k.val))).unit.app
    ((upperStar AddCommGrpCat.{u + 1}
      (D.map (show j.val ⟶ k.val from a).op)).obj (F j.val))).hom.naturality_assoc
    (γ j k a).inv.op]
  rw [← (eG k.val).inv.hom.naturality (δ k).inv.op]
  dsimp only [Functor.comp_obj]
  rw [lowerStar_obj_val_map]
  rw [← Functor.map_comp_assoc]
  rw [← ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op k.val))).map
    (φ (show j.val ⟶ k.val from a))).hom.naturality_assoc (δ k).inv.op]
  rw [← Functor.map_comp_assoc]
  -- Naturality leaves only the equality of the two restriction arrows.
  congr 2
  congr 2
  rw [← op_comp, ← op_comp]
  congr 1
  apply (cancel_epi (δ j).hom).1
  simp only [Iso.hom_inv_id_assoc]
  apply (cancel_mono
    ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op k.val))).map
      (γ j k a).hom ≫ (δ k).hom)).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  -- The first projections use hγ and hδ; the base projections agree automatically.
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc]
    rw [hδ k]
    simp only [MorphismProperty.Over.pullback_map_left, pullback.lift_fst_assoc]
    simp only [Category.assoc]
    rw [hγ j k a]
    rw [hδ j]
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
    erw [pullbackLeftPullbackSndIso_inv_fst_assoc]
    simp
  · simpa only [MorphismProperty.Over.pullback_obj_hom] using
      (MorphismProperty.Over.w
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
          (c.π.app (op k.val)) (D.map (show j.val ⟶ k.val from a).op)
          (c.π.app (op j.val)) (c.w (show j.val ⟶ k.val from a).op).symm).hom.app
          ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (homOfLE j.property).op)).obj T₀) ≫
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op k.val))).map
          (γ j k a).hom ≫ (δ k).hom)).trans (MorphismProperty.Over.w (δ j).hom).symm

end AlgebraicGeometry.Etale
