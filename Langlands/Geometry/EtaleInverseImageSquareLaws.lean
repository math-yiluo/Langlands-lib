import Langlands.Geometry.EtaleInverseImageExact
import Langlands.Geometry.EtaleInverseImageRestrictionCoherence

/-! # Identity and pasting for étale restriction of inverse image -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open EtalePullback EtaleDirectImage
open Langlands.Shimura.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R]

private abbrev smallEtaleModuleSheaves (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} R)

private abbrev etaleRestriction {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    smallEtaleModuleSheaves R X ⥤ smallEtaleModuleSheaves R Y :=
  restriction f (ModuleCat.{u} R)

local notation "Sh[" X "]" => smallEtaleModuleSheaves R X
local notation "I[" f "]" => inverseImage f R
local notation "E[" f "]" => etaleRestriction R f
local notation "C[" f "]" => inverseImageIsoRestriction f R

private theorem inverseImageCongr_trans {X Y : Scheme.{u}} {f g h : Y ⟶ X}
    (p : f = g) (q : g = h) :
    inverseImageCongr R (p.trans q) = inverseImageCongr R p ≪≫ inverseImageCongr R q := by
  cases p
  cases q
  simp only [inverseImageCongr_refl, Iso.refl_trans]

private theorem inverseImagePair_refl {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    projectionInverseImageIso R f _ g rfl = inverseImageComp R f g := by
  simp [projectionInverseImageIso, inverseImageCongr_refl]

private theorem inverseImagePair_assoc_app {X Y Z W : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z) {gf : Z ⟶ X} {hg : W ⟶ Y} {hgf : W ⟶ X}
    (p : g ≫ f = gf) (q : h ≫ g = hg) (r : h ≫ gf = hgf) (s : hg ≫ f = hgf) (F : Sh[X]) :
    I[h].map ((projectionInverseImageIso R f _ g p).hom.app F) ≫
        (projectionInverseImageIso R gf _ h r).hom.app F =
      (projectionInverseImageIso R g _ h q).hom.app (I[f].obj F) ≫
        (projectionInverseImageIso R f _ hg s).hom.app F := by
  cases p
  cases q
  cases r
  have H := congrArg (fun (α : (I[f] ⋙ I[g]) ⋙ I[h] ⟶ I[h ≫ g ≫ f]) => α.app F)
    (inverseImageComp_assoc R f g h)
  rw [inverseImagePair_refl R f g, inverseImagePair_refl R (g ≫ f) h,
    inverseImagePair_refl R g h]
  simpa only [projectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, associator_hom_app, Category.assoc, Category.id_comp] using H

/-- The two paths in a commuting square of scheme maps give canonically isomorphic
composites of geometric inverse images on small étale module sheaves. -/
def inverseImageSquare {X Y X' Y' : Scheme.{u}}
    (f : Y ⟶ X) (i : X' ⟶ X) (j : Y' ⟶ Y) (g : Y' ⟶ X') (h : j ≫ f = g ≫ i) :
    I[f] ⋙ I[j] ≅ I[i] ⋙ I[g] :=
  projectionInverseImageIso R f _ j h ≪≫ (inverseImageComp R i g).symm

@[reassoc]
private theorem inverseImageSquare_hom_pair {X Y X' Y' : Scheme.{u}}
    (f : Y ⟶ X) (i : X' ⟶ X) (j : Y' ⟶ Y) (g : Y' ⟶ X')
    (h : j ≫ f = g ≫ i) {k : Y' ⟶ X} (p : g ≫ i = k) (F : Sh[X]) :
    (inverseImageSquare R f i j g h).hom.app F ≫ (projectionInverseImageIso R i _ g p).hom.app F =
      (projectionInverseImageIso R f _ j (h.trans p)).hom.app F := by
  unfold inverseImageSquare projectionInverseImageIso
  rw [inverseImageCongr_trans R h p]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- The comparison with identity maps agrees with the canonical inverse-image units. -/
theorem inverseImageSquare_id {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : (𝟙 Y) ≫ f = f ≫ 𝟙 X) (F : Sh[X]) :
    (inverseImageSquare R f (𝟙 X) (𝟙 Y) f h).hom.app F ≫
        I[f].map ((inverseImageId R X).hom.app F) =
      (inverseImageId R Y).hom.app (I[f].obj F) := by
  have ht := congrArg (fun m => NatTrans.app m F) (inverseImageComp_id_target R f)
  have hs := congrArg (fun m => NatTrans.app m F) (inverseImageComp_id_source R f)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, leftUnitor_hom_app,
    rightUnitor_hom_app] at ht hs
  change (projectionInverseImageIso R (𝟙 X) _ f (Category.comp_id f)).hom.app F = _ at ht
  rw [← ht.trans (Category.comp_id _), inverseImageSquare_hom_pair]
  exact hs.trans (Category.comp_id _)

/-- Pasting commuting squares agrees with composing their inverse-image comparisons. -/
theorem inverseImageSquare_comp {X Y X' Y' X'' Y'' : Scheme.{u}}
    (f : Y ⟶ X) (i : X' ⟶ X) (j : Y' ⟶ Y) (g : Y' ⟶ X') (h : j ≫ f = g ≫ i)
    (i' : X'' ⟶ X') (j' : Y'' ⟶ Y') (g' : Y'' ⟶ X'') (h' : j' ≫ g = g' ≫ i')
    (hc : (j' ≫ j) ≫ f = g' ≫ i' ≫ i) (F : Sh[X]) :
    I[j'].map ((inverseImageSquare R f i j g h).hom.app F) ≫
        (inverseImageSquare R g i' j' g' h').hom.app (I[i].obj F) ≫
        I[g'].map ((inverseImageComp R i i').hom.app F) =
      (inverseImageComp R j j').hom.app (I[f].obj F) ≫
        (inverseImageSquare R f (i' ≫ i) (j' ≫ j) g' hc).hom.app F := by
  let k := g' ≫ i' ≫ i
  have hk : j' ≫ (g ≫ i) = k := by
    rw [← Category.assoc, h', Category.assoc]
  apply (cancel_mono ((inverseImageComp R (i' ≫ i) g').hom.app F)).mp
  simp only [Category.assoc]
  rw [← inverseImagePair_refl R (i' ≫ i) g', ← inverseImagePair_refl R i i']
  rw [inverseImagePair_assoc_app R i i' g' rfl rfl rfl (Category.assoc g' i' i)]
  rw [inverseImageSquare_hom_pair_assoc R g i' j' g' h' rfl]
  rw [← inverseImagePair_assoc_app R i g j' rfl h' hk (Category.assoc g' i' i) F]
  rw [← I[j'].map_comp_assoc, inverseImageSquare_hom_pair R f i j g h rfl]
  rw [inverseImagePair_assoc_app R f j j' h rfl hk hc F]
  rw [inverseImageSquare_hom_pair R f (i' ≫ i) (j' ≫ j) g' hc rfl]
  rw [inverseImagePair_refl]

@[reassoc]
private theorem inverseImageRestrictionSquare_compare {X Y X' Y' : Scheme.{u}}
    (f : Y ⟶ X) (i : X' ⟶ X) [Etale i] (j : Y' ⟶ Y) [Etale j] (g : Y' ⟶ X')
    (h : j ≫ f = g ≫ i) (F : Sh[X]) :
    C[j].hom.app (I[f].obj F) ≫ (inverseImageRestrictionSquare R f i j g h).hom.app F =
      (inverseImageSquare R f i j g h).hom.app F ≫ I[g].map (C[i].hom.app F) := by
  simp only [inverseImageRestrictionSquare, inverseImageSquare, projectionInverseImageIso, Iso.trans_hom,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem inverseImageIsoRestriction_id_app (X : Scheme.{u}) (F : Sh[X]) :
    C[𝟙 X].hom.app F ≫ (restrictionId (X := X) (ModuleCat.{u} R)).hom.app F =
      (inverseImageId R X).hom.app F :=
  congrArg (fun m => NatTrans.app m F) (inverseImageIsoRestriction_id R X)

private theorem inverseImageIsoRestriction_comp_app
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [Etale f] (g : Z ⟶ Y) [Etale g] (F : Sh[X]) :
    (inverseImageComp R f g).hom.app F ≫ C[g ≫ f].hom.app F =
      (I[g].map (C[f].hom.app F) ≫ C[g].hom.app (E[f].obj F)) ≫
        (restrictionComp f (ModuleCat.{u} R) g).hom.app F := by
  simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] using
    congrArg (fun m => NatTrans.app m F) (inverseImageIsoRestriction_comp R f g)

/-- With identity étale arrows, the commuting-square comparison agrees with the two
identity restriction maps. -/
theorem inverseImageRestrictionSquare_id {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : (𝟙 Y) ≫ f = f ≫ 𝟙 X) (F : Sh[X]) :
    (inverseImageRestrictionSquare R f (𝟙 X) (𝟙 Y) f h).hom.app F ≫
        I[f].map ((restrictionId (X := X) (ModuleCat.{u} R)).hom.app F) =
      (restrictionId (X := Y) (ModuleCat.{u} R)).hom.app (I[f].obj F) := by
  let e := C[𝟙 Y].app (I[f].obj F)
  apply (Iso.cancel_iso_hom_left e _ _).mp
  simp only [e, Iso.app_hom]
  rw [inverseImageRestrictionSquare_compare_assoc R f (𝟙 X) (𝟙 Y) f h F]
  have hm := (I[f]).map_comp (C[𝟙 X].hom.app F)
    ((restrictionId (X := X) (ModuleCat.{u} R)).hom.app F)
  erw [← hm, inverseImageIsoRestriction_id_app R X F,
    inverseImageIsoRestriction_id_app R Y (I[f].obj F)]
  exact inverseImageSquare_id R f h F

/-- The comparisons for successive étale restriction squares agree with the comparison
for their pasted square, through the canonical restriction composition maps. -/
theorem inverseImageRestrictionSquare_comp {X Y X' Y' X'' Y'' : Scheme.{u}}
    (f : Y ⟶ X) (i : X' ⟶ X) [Etale i] (j : Y' ⟶ Y) [Etale j]
    (g : Y' ⟶ X') (h : j ≫ f = g ≫ i)
    (i' : X'' ⟶ X') [Etale i'] (j' : Y'' ⟶ Y') [Etale j']
    (g' : Y'' ⟶ X'') (h' : j' ≫ g = g' ≫ i')
    (hc : (j' ≫ j) ≫ f = g' ≫ i' ≫ i) (F : Sh[X]) :
    E[j'].map ((inverseImageRestrictionSquare R f i j g h).hom.app F) ≫
        (inverseImageRestrictionSquare R g i' j' g' h').hom.app (E[i].obj F) ≫
        I[g'].map ((restrictionComp i (ModuleCat.{u} R) i').hom.app F) =
      (restrictionComp j (ModuleCat.{u} R) j').hom.app (I[f].obj F) ≫
        (inverseImageRestrictionSquare R f (i' ≫ i) (j' ≫ j) g' hc).hom.app F := by
  let e := I[j'].mapIso (C[j].app (I[f].obj F)) ≪≫ C[j'].app (E[j].obj (I[f].obj F))
  apply (Iso.cancel_iso_hom_left e _ _).mp
  simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  trans (I[j'].map ((inverseImageSquare R f i j g h).hom.app F) ≫
      (inverseImageSquare R g i' j' g' h').hom.app (I[i].obj F) ≫
      I[g'].map ((inverseImageComp R i i').hom.app F)) ≫ I[g'].map (C[i' ≫ i].hom.app F)
  · simp only [Category.assoc]
    rw [← C[j'].hom.naturality_assoc, ← I[j'].map_comp_assoc,
      inverseImageRestrictionSquare_compare, I[j'].map_comp, Category.assoc]
    simp only [Functor.comp_obj]
    rw [inverseImageRestrictionSquare_compare_assoc R g i' j' g' h' (E[i].obj F)]
    have hn := (inverseImageSquare R g i' j' g' h').hom.naturality_assoc (C[i].hom.app F)
      (I[g'].map (C[i'].hom.app (E[i].obj F)) ≫
        I[g'].map ((restrictionComp i (ModuleCat.{u} R) i').hom.app F))
    simp only [Functor.comp_map] at hn
    rw [hn, ← I[g'].map_comp_assoc, ← I[g'].map_comp, ← inverseImageIsoRestriction_comp_app,
      I[g'].map_comp]
  · rw [inverseImageSquare_comp R f i j g h i' j' g' h' hc F]
    have hm := congrArg
      (· ≫ (inverseImageRestrictionSquare R f (i' ≫ i) (j' ≫ j) g' hc).hom.app F)
      (inverseImageIsoRestriction_comp_app R j j' (I[f].obj F))
    simp only [Category.assoc] at hm ⊢
    rw [← hm]
    rw [inverseImageRestrictionSquare_compare R f (i' ≫ i) (j' ≫ j) g' hc F]

/-- The étale restriction square respects equality transport in the two étale maps. -/
theorem inverseImageRestrictionSquare_congr {X Y X' Y' : Scheme.{u}}
    (f : Y ⟶ X) {i i₁ : X' ⟶ X} [Etale i] [Etale i₁]
    {j j₁ : Y' ⟶ Y} [Etale j] [Etale j₁] (g : Y' ⟶ X')
    (h : j ≫ f = g ≫ i) (h₁ : j₁ ≫ f = g ≫ i₁)
    (eᵢ : i = i₁) (eⱼ : j = j₁) (F : Sh[X]) :
    (restrictionCongr R eⱼ).hom.app (I[f].obj F) ≫
        (inverseImageRestrictionSquare R f i₁ j₁ g h₁).hom.app F =
      (inverseImageRestrictionSquare R f i j g h).hom.app F ≫
        I[g].map ((restrictionCongr R eᵢ).hom.app F) := by
  subst i₁
  subst j₁
  simp [restrictionCongr]

end Langlands.Geometry.EtaleInverseImage
