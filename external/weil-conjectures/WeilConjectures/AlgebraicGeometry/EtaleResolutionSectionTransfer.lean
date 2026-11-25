/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSectionComplex

/-!
# Sections of a comparison into a direct image resolution

Source: Stacks Project, Tag 0A50, proof.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate a complex morphism into a direct image, then restrict along a chosen
map to the corresponding fibre product. This is an explicit chain map. 
(blueprint: def-weil-pbc-etale-resolution-section-transfer)
-/
noncomputable def resolutionSectionTransfer {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (α : K ⟶ ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj L)
    (A : X.Etale) (B : Y.Etale)
    (k : B ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj A) :
    ((etaleSectionFunctor A).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((etaleSectionFunctor B).mapHomologicalComplex (.up ℕ)).obj L where
  f n := (α.f n).hom.app (op A) ≫ (L.X n).obj.map k.op
  comm' i j hij := by
    have h := congrArg (fun f ↦ f.hom.app (op A)) (α.comm i j)
    change (α.f i).hom.app (op A) ≫ (L.X i).obj.map k.op ≫
      (L.d i j).hom.app (op B) =
      (K.d i j).hom.app (op A) ≫ (α.f j).hom.app (op A) ≫ (L.X j).obj.map k.op
    rw [(L.d i j).hom.naturality k.op, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ (L.X j).obj.map k.op) h

set_option backward.isDefEq.respectTransparency false in
/-- Section transfers commute with restriction whenever the site square commutes. 
(blueprint: def-weil-pbc-etale-resolution-section-transfer)
-/
theorem resolutionSectionTransfer_naturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (α : K ⟶ ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj L)
    {A A' : X.Etale} {B B' : Y.Etale} (a : A ⟶ A') (b : B ⟶ B')
    (k : B ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj A)
    (k' : B' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj A')
    (h : b ≫ k' = k ≫ (MorphismProperty.Over.pullback @Etale ⊤ g).map a) :
    etaleSectionMap a K ≫ resolutionSectionTransfer g K L α A B k =
      resolutionSectionTransfer g K L α A' B' k' ≫ etaleSectionMap b L := by
  apply HomologicalComplex.hom_ext
  intro n
  change (K.X n).obj.map a.op ≫ (α.f n).hom.app (op A) ≫ (L.X n).obj.map k.op =
    ((α.f n).hom.app (op A') ≫ (L.X n).obj.map k'.op) ≫ (L.X n).obj.map b.op
  rw [← Category.assoc, (α.f n).hom.naturality a.op]
  simp only [Category.assoc]
  change (α.f n).hom.app (op A') ≫
    (L.X n).obj.map ((MorphismProperty.Over.pullback @Etale ⊤ g).map a).op ≫
      (L.X n).obj.map k.op = _
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h]

/-- The terminal étale object maps to its base change along g. 
(blueprint: def-weil-pbc-etale-resolution-section-transfer)
-/
noncomputable def terminalSectionPullback {X Y : Scheme.{u}} (g : Y ⟶ X) :
    Scheme.Etale.mk (𝟙 Y) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk (𝟙 X)) :=
  MorphismProperty.Over.homMk
    (pullback.lift g (𝟙 Y) ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp)

/-- The inverse-image open maps to the base change of the original open. 
(blueprint: def-weil-pbc-etale-resolution-section-transfer)
-/
noncomputable def openSectionPullback {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens) :
    Scheme.Etale.mk (g ⁻¹ᵁ W).ι ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk W.ι) :=
  MorphismProperty.Over.homMk
    (pullback.lift (morphismRestrict g W) (g ⁻¹ᵁ W).ι (morphismRestrict_ι g W)) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Transfer on sections of a whole scheme. 
(blueprint: def-weil-pbc-etale-resolution-section-transfer)
-/
noncomputable abbrev globalResolutionSectionTransfer {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (α : K ⟶ ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj L) :=
  resolutionSectionTransfer g K L α (Scheme.Etale.mk (𝟙 X))
    (Scheme.Etale.mk (𝟙 Y)) (terminalSectionPullback g)

set_option backward.isDefEq.respectTransparency false in
/-- Transfer on sections over an open. 
(blueprint: def-weil-pbc-etale-resolution-section-transfer)
-/
noncomputable abbrev openResolutionSectionTransfer {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (α : K ⟶ ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj L)
    (W : X.Opens) :=
  resolutionSectionTransfer g K L α (Scheme.Etale.mk W.ι)
    (Scheme.Etale.mk (g ⁻¹ᵁ W).ι) (openSectionPullback g W)

set_option backward.isDefEq.respectTransparency false in
theorem terminalSectionPullback_naturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    (W : X.Opens) :
    (MorphismProperty.Over.homMk (g ⁻¹ᵁ W).ι (Category.comp_id _) :
      Scheme.Etale.mk (g ⁻¹ᵁ W).ι ⟶ Scheme.Etale.mk (𝟙 Y)) ≫ terminalSectionPullback g =
      openSectionPullback g W ≫ (MorphismProperty.Over.pullback @Etale ⊤ g).map
        (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
          Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) := by
  apply MorphismProperty.Over.Hom.ext
  change (g ⁻¹ᵁ W).ι ≫ pullback.lift g (𝟙 Y) _ =
    pullback.lift (morphismRestrict g W) (g ⁻¹ᵁ W).ι _ ≫
      pullback.lift (pullback.fst W.ι g ≫ W.ι) (pullback.snd W.ι g) _
  apply pullback.hom_ext <;> simp [morphismRestrict_ι]

set_option backward.isDefEq.respectTransparency false in
theorem openSectionPullback_naturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A B : X.Opens} (h : A ≤ B) :
    (MorphismProperty.Over.homMk (Y.homOfLE (g.preimage_mono h)) (Y.homOfLE_ι _) :
      Scheme.Etale.mk (g ⁻¹ᵁ A).ι ⟶ Scheme.Etale.mk (g ⁻¹ᵁ B).ι) ≫
        openSectionPullback g B =
      openSectionPullback g A ≫ (MorphismProperty.Over.pullback @Etale ⊤ g).map
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) := by
  apply MorphismProperty.Over.Hom.ext
  change Y.homOfLE (g.preimage_mono h) ≫
    pullback.lift (morphismRestrict g B) (g ⁻¹ᵁ B).ι _ =
      pullback.lift (morphismRestrict g A) (g ⁻¹ᵁ A).ι _ ≫
        pullback.lift (pullback.fst A.ι g ≫ X.homOfLE h) (pullback.snd A.ι g) _
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    apply (cancel_mono B.ι).1
    simp [morphismRestrict_ι]
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- The explicit morphism of restriction-pair/difference section complexes induced by a
complex morphism into the direct image. This construction requires no covering assumption.
Source: Stacks Project, Tag 0A50, proof.
(blueprint: def-weil-pbc-etale-resolution-section-transfer) -/
noncomputable def resolutionSectionShortComplexTransfer {X Y : Scheme.{u}} (g : Y ⟶ X)
    (U V : X.Opens)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (L : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (α : K ⟶ ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj L) :
    etaleSectionShortComplex U V K ⟶
      etaleSectionShortComplex (g ⁻¹ᵁ U) (g ⁻¹ᵁ V) L where
  τ₁ := globalResolutionSectionTransfer g K L α
  τ₂ := biprod.map (openResolutionSectionTransfer g K L α U)
    (openResolutionSectionTransfer g K L α V)
  τ₃ := openResolutionSectionTransfer g K L α (U ⊓ V)
  comm₁₂ := by
    apply biprod.hom_ext
    · simpa [etaleSectionShortComplex] using
        resolutionSectionTransfer_naturality g K L α _ _ _ _
          (terminalSectionPullback_naturality g U) |>.symm
    · simpa [etaleSectionShortComplex] using
        resolutionSectionTransfer_naturality g K L α _ _ _ _
          (terminalSectionPullback_naturality g V) |>.symm
  comm₂₃ := by
    apply biprod.hom_ext'
    · simpa [etaleSectionShortComplex] using
        resolutionSectionTransfer_naturality g K L α _ _ _ _
          (openSectionPullback_naturality g (inf_le_left : U ⊓ V ≤ U)) |>.symm
    · simpa [etaleSectionShortComplex] using
        congrArg Neg.neg (resolutionSectionTransfer_naturality g K L α _ _ _ _
          (openSectionPullback_naturality g (inf_le_right : U ⊓ V ≤ V))) |>.symm

end AlgebraicGeometry.Etale
