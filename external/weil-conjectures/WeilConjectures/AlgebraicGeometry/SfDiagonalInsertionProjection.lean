/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import WeilConjectures.AlgebraicGeometry.SfDiagonalPushComparison
import WeilConjectures.AlgebraicGeometry.SfProperSectionProjection

/-! # Projection naturality for insertion of a supported diagonal class

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, projection naturality and the two diagonal section identities.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Check the large comparison identities sequentially.
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SupportedTrace

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

-- Reassociate with abstract functors, then specialize to the canonical comparison maps.
-- This avoids unfolding compactification constructions during kernel conversion.
private theorem first_assembly
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P Q : E ⥤ C) (c : Q ⋙ F ≅ P ⋙ F)
    {M N N' : C} {S U V : E}
    (a : (𝟭 C).obj M ⟶ Q.obj S) (b : (𝟭 C).obj M ⟶ P.obj S)
    (k : S ⟶ U) (r : U ⟶ V)
    (p : N ≅ P.obj U) (q : N' ≅ P.obj V) (t : N ⟶ N') (z : M ⟶ N)
    (hc : F.map a ≫ c.hom.app S = F.map b)
    (hu : b ≫ P.map k = z ≫ p.hom)
    (hn : P.map r ≫ q.inv = p.inv ≫ t) :
    F.map (a ≫ Q.map k ≫ Q.map r) ≫ c.hom.app V ≫ F.map q.inv =
      F.map (z ≫ t) := by
  have hnat := c.hom.naturality (k ≫ r)
  dsimp only [Functor.comp_map] at hnat
  calc
    _ = F.map a ≫ (F.map (Q.map (k ≫ r)) ≫ c.hom.app V) ≫ F.map q.inv := by
      simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
    _ = (F.map a ≫ c.hom.app S) ≫ F.map (P.map k ≫ P.map r ≫ q.inv) := by
      rw [hnat]
      simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
    _ = F.map (b ≫ P.map k ≫ P.map r ≫ q.inv) := by
      rw [hc]
      simp -implicitDefEqProofs only [Functor.map_comp]
    _ = _ := by
      congr 1
      rw [hn, ← Category.assoc, hu]
      simp -implicitDefEqProofs only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem second_assembly
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {M N N' : D} {S U U' V V' : C}
    (a : (𝟭 D).obj M ⟶ P.obj S) (k : S ⟶ U) (r : U ⟶ V)
    (v : V ⟶ V') (w : U ⟶ U') (r' : U' ⟶ V')
    (p : N ≅ P.obj U') (q : N' ≅ P.obj V') (t : N ⟶ N') (z : M ⟶ N)
    (hv : r ≫ v = w ≫ r')
    (hu : a ≫ P.map (k ≫ w) = z ≫ p.hom)
    (hn : P.map r' ≫ q.inv = p.inv ≫ t) :
    (a ≫ P.map k ≫ P.map r) ≫ P.map v ≫ q.inv = z ≫ t := by
  calc
    _ = a ≫ P.map k ≫ P.map (r ≫ v) ≫ q.inv := by
      simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
    _ = (a ≫ P.map (k ≫ w)) ≫ (P.map r' ≫ q.inv) := by
      rw [hv]
      simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [hu, hn]
      simp -implicitDefEqProofs only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem first_insertion_assembly
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P Q : E ⥤ C) (c : Q ⋙ F ≅ P ⋙ F) (G : C ⥤ C)
    {M one : C} {S U V U₀ V₀ : E}
    (a : (𝟭 C).obj M ⟶ Q.obj S) (b : (𝟭 C).obj M ⟶ P.obj S)
    (k : S ⟶ U) (r : U ⟶ V)
    (p : G.obj (P.obj U₀) ≅ P.obj U) (q : G.obj (P.obj V₀) ≅ P.obj V)
    (ρ : M ⟶ G.obj one) (v₀ : one ⟶ P.obj U₀) (δ : U₀ ⟶ V₀)
    (i : (𝟭 C).obj M ⟶ Q.obj V)
    (hi : i = a ≫ Q.map k ≫ Q.map r)
    (hc : F.map a ≫ c.hom.app S = F.map b)
    (hu : b ≫ P.map k = ρ ≫ G.map v₀ ≫ p.hom)
    (hn : P.map r ≫ q.inv = p.inv ≫ G.map (P.map δ)) :
    F.map i ≫ c.hom.app V ≫ F.map q.inv = F.map (ρ ≫ G.map (v₀ ≫ P.map δ)) := by
  rw [hi]
  have h := first_assembly F P Q c a b k r p q (G.map (P.map δ))
    (ρ ≫ G.map v₀) hc (by simpa only [Category.assoc] using hu) hn
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem second_insertion_assembly
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D) (G : D ⥤ D)
    {M one : D} {S H U U' V V' U₀ V₀ : C}
    (a : (𝟭 D).obj M ⟶ P.obj S) (k : S ⟶ H) (s : H ⟶ U) (r : U ⟶ V)
    (v : V ⟶ V') (w : U ⟶ U') (r' : U' ⟶ V') (u : S ⟶ U')
    (p : G.obj (P.obj U₀) ≅ P.obj U') (q : G.obj (P.obj V₀) ≅ P.obj V')
    (ρ : M ⟶ G.obj one) (v₀ : one ⟶ P.obj U₀) (δ : U₀ ⟶ V₀)
    (i : (𝟭 D).obj M ⟶ P.obj V)
    (hi : i = a ≫ P.map (k ≫ s) ≫ P.map r)
    (hv : r ≫ v = w ≫ r') (ht : k ≫ s ≫ w = u)
    (hu : a ≫ P.map u = ρ ≫ G.map v₀ ≫ p.hom)
    (hn : P.map r' ≫ q.inv = p.inv ≫ G.map (P.map δ)) :
    i ≫ P.map v ≫ q.inv = ρ ≫ G.map (v₀ ≫ P.map δ) := by
  rw [hi]
  have hu' : a ≫ P.map ((k ≫ s) ≫ w) = (ρ ≫ G.map v₀) ≫ p.hom := by
    rw [Category.assoc, ht]
    simpa only [Category.assoc] using hu
  have h := second_assembly P a (k ≫ s) r v w r' p q (G.map (P.map δ))
    (ρ ≫ G.map v₀) hv hu' hn
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem section_tensor_coordinate
    {C D : Type*} [Category C] [Category D]
    (P₁ P₂ : C ⥤ D) (R : D ⥤ C) (S : C ⥤ D) (T : D ⥤ D ⥤ D)
    (U : D) (σ : T ≅ T.flip) (π : R ⋙ S ≅ T.obj U)
    (l₁ : 𝟭 C ≅ P₁ ⋙ R) (l₂ : P₂ ⋙ R ≅ 𝟭 C)
    (κ₁ : S ≅ P₁ ⋙ T.obj U) (κ₂ : S ≅ P₂ ⋙ T.obj U)
    (hκ₁ : κ₁ = ((Functor.leftUnitor S).symm ≪≫
      Functor.isoWhiskerRight l₁ S ≪≫ Functor.associator P₁ R S) ≪≫
        Functor.isoWhiskerLeft P₁ π)
    (hκ₂ : κ₂ = ((Functor.leftUnitor S).symm ≪≫
      Functor.isoWhiskerRight l₂.symm S ≪≫ Functor.associator P₂ R S) ≪≫
        Functor.isoWhiskerLeft P₂ π)
    (M : C) (c : P₁.obj M ⟶ P₂.obj M)
    (hl : l₁.hom.app M ≫ R.map c = l₂.inv.app M) :
    κ₁.hom.app M ≫ ((σ.app U).app (P₁.obj M)).hom ≫ (T.map c).app U =
      κ₂.hom.app M ≫ ((σ.app U).app (P₂.obj M)).hom := by
  subst κ₁ κ₂
  have hs := (σ.hom.app U).naturality c
  have hp := π.hom.naturality c
  dsimp only [Functor.comp_map] at hp
  simp only [Functor.flip_obj_map] at hs
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Category.id_comp, Iso.app_hom, Category.assoc]
  rw [← hs, ← reassoc_of% hp, ← S.map_comp_assoc, hl]

section Naturality

-- Follow the source's component API in fixing the derived-category instances.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

attribute [local irreducible]
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor derivedTensorSymmetry
  rightDerivedLowerShriekCompIso rightDerivedLowerShriekCongrIso
  rightDerivedLowerShriekIdIsoOfLowerStar leftDerivedUpperStarComp leftDerivedUpperStarId
attribute [local implicit_reducible] rightDerivedLowerShriek derivedTensorRight
attribute [local irreducible] TraceDiagonalDatum.diagonalIso TraceDiagonalDatum.idIsoDiagonalSnd
  projectionUnitIso projectionMap SfDiagonalKernel.diagonalFirst
  properSectionPushIso properSectionTensorIso directComparison unitRightUnitor

private local instance : IsProper (TraceDiagonalDatum.diagonal f) := by
  change IsProper (pullback.diagonal f)
  infer_instance

private theorem section_unit_of_isos {X W : Scheme.{u}} (s : X ⟶ W) (p : W ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X)
    (α : 𝟭 (DerivedCategoryModule A X) ≅ push A s ⋙ push A p)
    (hα : properSectionPushIso A s p h = α)
    (κ : push A s ≅ CoordinateTrace.pull A p ⋙
      (derivedTensor (ModuleCat.{u + 1} A) W).obj
        ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X)))
    (hκ : properSectionTensorIso A s p h = κ) (M : DerivedCategoryModule A X) :
    α.hom.app M ≫ (push A p).map
        (κ.hom.app M ≫ (CoordinateTrace.swap A W
          ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))
          ((CoordinateTrace.pull A p).obj M)).hom) =
      (unitRightUnitor (ModuleCat.{u + 1} A) X M).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          (α.hom.app (derivedTensorUnit (ModuleCat.{u + 1} A) X)) ≫
        (orderedProjection A p M
          ((push A s).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X))).hom := by
  subst α κ
  exact properSectionProjectionUnit A s p h M

private theorem sectionPush_first :
    properSectionPushIso A (TraceDiagonalDatum.diagonal f) (pullback.fst f f)
      (TraceDiagonalDatum.diagonal_fst f) = SfDiagonalKernel.diagonalFirst A f := by
  unfold properSectionPushIso SfDiagonalKernel.diagonalFirst
  rfl

private theorem sectionPush_second :
    properSectionPushIso A (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
      (TraceDiagonalDatum.diagonal_snd f) =
      TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f := by
  unfold properSectionPushIso TraceDiagonalDatum.idIsoDiagonalSnd
  rfl

private theorem sectionTensor_first :
    properSectionTensorIso A (TraceDiagonalDatum.diagonal f) (pullback.fst f f)
      (TraceDiagonalDatum.diagonal_fst f) = TraceDiagonalDatum.diagonalIso (Λ := A) f := by
  unfold properSectionTensorIso TraceDiagonalDatum.diagonalIso
    TraceDiagonalDatum.diagonalLowerShriekSectionIso TraceDiagonalDatum.diagonalSectionIso
  rfl

private theorem orderedProjection_naturality {W Z : Scheme.{u}}
    (p : W ⟶ Z) [HasCompactification p] (M : DerivedCategoryModule A Z)
    {E E' : DerivedCategoryModule A W} (v : E ⟶ E') :
    (push A p).map (((derivedTensor (ModuleCat.{u + 1} A) W).obj
        ((CoordinateTrace.pull A p).obj M)).map v) ≫
        (orderedProjection A p M E').inv =
      (orderedProjection A p M E).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj M).map ((push A p).map v) := by
  apply (cancel_epi (orderedProjection A p M E).hom).1
  apply (cancel_mono (orderedProjection A p M E').hom).1
  simp -implicitDefEqProofs only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc]
  dsimp only [orderedProjection, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  have hs := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app M).naturality
    ((push A p).map v)
  have hp := NatTrans.congr_app ((projectionMap (ModuleCat.{u + 1} A) p).naturality v) M
  have ht := NatTrans.congr_app
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) W).hom.naturality v)
    ((CoordinateTrace.pull A p).obj M)
  change ((derivedTensor (ModuleCat.{u + 1} A) Z).obj M).map ((push A p).map v) ≫
      (CoordinateTrace.swap A Z M ((push A p).obj E')).hom =
    (CoordinateTrace.swap A Z M ((push A p).obj E)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z).map ((push A p).map v)).app M at hs
  change ((derivedTensor (ModuleCat.{u + 1} A) Z).map ((push A p).map v)).app M ≫
      (projectionIso A p E').hom.app M =
    (projectionIso A p E).hom.app M ≫
      (push A p).map (((derivedTensor (ModuleCat.{u + 1} A) W).map v).app
        ((CoordinateTrace.pull A p).obj M)) at hp
  change ((derivedTensor (ModuleCat.{u + 1} A) W).map v).app
      ((CoordinateTrace.pull A p).obj M) ≫
      (CoordinateTrace.swap A W E' ((CoordinateTrace.pull A p).obj M)).hom =
    (CoordinateTrace.swap A W E ((CoordinateTrace.pull A p).obj M)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) W).obj
        ((CoordinateTrace.pull A p).obj M)).map v at ht
  simp -implicitDefEqProofs only [Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hp]
  simp -implicitDefEqProofs only [← (push A p).map_comp, ht]

private theorem insertion_nat_factor {B : DerivedCategoryModule A X}
    (δ : (push A (TraceDiagonalDatum.diagonal f)).obj
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
      (CoordinateTrace.pull A (pullback.snd f f)).obj B) :
    insertion A f δ =
      (TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom ≫
        Functor.whiskerRight (TraceDiagonalDatum.diagonalIso (Λ := A) f).hom
          (push A (pullback.snd f f)) ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (CoordinateTrace.pull A (pullback.fst f f))
            (((derivedTensorSymmetry (ModuleCat.{u + 1} A) (pullback f f)).hom.app
              ((push A (TraceDiagonalDatum.diagonal f)).obj
                (derivedTensorUnit (ModuleCat.{u + 1} A) X))) ≫
            (derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).flip.map δ))
          (push A (pullback.snd f f)) := by
  simp only [insertion, Iso.app_hom]
  rw [(derivedTensorSymmetry (ModuleCat.{u + 1} A) (pullback f f)).hom.naturality δ]

private theorem insertionApp_factor {B : DerivedCategoryModule A X}
    (δ : (push A (TraceDiagonalDatum.diagonal f)).obj
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
      (CoordinateTrace.pull A (pullback.snd f f)).obj B)
    (M : DerivedCategoryModule A X) :
    insertionApp A f (B := B) δ M =
      (TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app M ≫
        (push A (pullback.snd f f)).map
          ((TraceDiagonalDatum.diagonalIso (Λ := A) f).hom.app M ≫
            (CoordinateTrace.swap A (pullback f f)
              ((push A (TraceDiagonalDatum.diagonal f)).obj
                (derivedTensorUnit (ModuleCat.{u + 1} A) X))
              ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).hom) ≫
        (push A (pullback.snd f f)).map
          (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).obj
            ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).map δ)  := by
  unfold insertionApp
  rw [insertion_nat_factor]
  simp -implicitDefEqProofs only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.flip_map_app, CoordinateTrace.swap,
    Iso.app_hom, Functor.map_comp, Category.assoc]

omit [Finite A] [IsProper f] in
private theorem diagonal_coordinate_base (N : DerivedCategoryModule A Y) :
    (TraceDiagonalDatum.diagonalSectionIso (Λ := A) f).hom.app
        ((CoordinateTrace.pull A f).obj N) ≫
      (CoordinateTrace.pull A (TraceDiagonalDatum.diagonal f)).map
        (CoordinateTrace.coordinate A f N).hom =
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
      (TraceDiagonalDatum.diagonal_snd f)).inv.app ((CoordinateTrace.pull A f).obj N) := by
  have h1 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    (TraceDiagonalDatum.diagonal f) (pullback.fst f f) f (𝟙 X)
    (pullback.snd f f ≫ f) f (TraceDiagonalDatum.diagonal_fst f).symm
    (pullback.condition (f := f) (g := f)).symm (Category.id_comp f).symm N
  have h2 := leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    (TraceDiagonalDatum.diagonal f) (pullback.snd f f) f (𝟙 X)
    (pullback.snd f f ≫ f) f (TraceDiagonalDatum.diagonal_snd f).symm
    rfl (Category.id_comp f).symm N
  simp -implicitDefEqProofs only [TraceDiagonalDatum.diagonalSectionIso,
    leftDerivedUpperStarCompSectionIso,
    CoordinateTrace.coordinate, derivedSquareUpperStarIso,
    Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, NatTrans.comp_app,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).inv.app
    ((CoordinateTrace.pull A f).obj N))).2
  apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (𝟙 X) f f (Category.id_comp f).symm).hom.app N)).1
  rw [← reassoc_of% h1, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp -implicitDefEqProofs only [CategoryTheory.Functor.map_id, Category.id_comp]
  exact h2

omit [Finite A] [IsProper f] in
private theorem diagonal_coordinate {B : DerivedCategoryModule A X}
    (N : DerivedCategoryModule A Y) (e : B ≅ (CoordinateTrace.pull A f).obj N) :
    (TraceDiagonalDatum.diagonalSectionIso (Λ := A) f).hom.app B ≫
      (CoordinateTrace.pull A (TraceDiagonalDatum.diagonal f)).map
        (SfDiagonalKernel.coordinate A f N e).hom =
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
      (TraceDiagonalDatum.diagonal_snd f)).inv.app B := by
  have h1 := (TraceDiagonalDatum.diagonalSectionIso (Λ := A) f).hom.naturality e.hom
  have h2 := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
    (TraceDiagonalDatum.diagonal_snd f)).inv.naturality e.inv
  dsimp only [Functor.id_map, Functor.comp_map] at h1 h2
  simp -implicitDefEqProofs only [SfDiagonalKernel.coordinate, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp]
  rw [← reassoc_of% h1, reassoc_of% diagonal_coordinate_base A f N, ← h2]
  simp -implicitDefEqProofs only [← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem diagonal_tensor_second {B : DerivedCategoryModule A X}
    (N : DerivedCategoryModule A Y) (e : B ≅ (CoordinateTrace.pull A f).obj N) :
    (TraceDiagonalDatum.diagonalIso (Λ := A) f).hom.app B ≫
      (CoordinateTrace.swap A (pullback f f)
        ((push A (TraceDiagonalDatum.diagonal f)).obj
          (derivedTensorUnit (ModuleCat.{u + 1} A) X))
        ((CoordinateTrace.pull A (pullback.fst f f)).obj B)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
        (SfDiagonalKernel.coordinate A f N e).hom).app
          ((push A (TraceDiagonalDatum.diagonal f)).obj
            (derivedTensorUnit (ModuleCat.{u + 1} A) X)) =
    (properSectionTensorIso A (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
      (TraceDiagonalDatum.diagonal_snd f)).hom.app B ≫
      (CoordinateTrace.swap A (pullback f f)
        ((push A (TraceDiagonalDatum.diagonal f)).obj
          (derivedTensorUnit (ModuleCat.{u + 1} A) X))
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).hom := by
  exact section_tensor_coordinate (CoordinateTrace.pull A (pullback.fst f f))
    (CoordinateTrace.pull A (pullback.snd f f))
    (CoordinateTrace.pull A (TraceDiagonalDatum.diagonal f))
    (push A (TraceDiagonalDatum.diagonal f))
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f f))
    ((push A (TraceDiagonalDatum.diagonal f)).obj
      (derivedTensorUnit (ModuleCat.{u + 1} A) X))
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) (pullback f f))
    (projectionUnitIso A (TraceDiagonalDatum.diagonal f))
    (TraceDiagonalDatum.diagonalSectionIso (Λ := A) f)
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
      (TraceDiagonalDatum.diagonal_snd f))
    (TraceDiagonalDatum.diagonalIso (Λ := A) f)
    (properSectionTensorIso A (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
      (TraceDiagonalDatum.diagonal_snd f))
    (by
      unfold TraceDiagonalDatum.diagonalIso
        TraceDiagonalDatum.diagonalLowerShriekSectionIso
      rfl)
    (by unfold properSectionTensorIso; rfl) B
    (SfDiagonalKernel.coordinate A f N e).hom (diagonal_coordinate A f N e)

private theorem diagonalFirst_unit (M : DerivedCategoryModule A X) :
    (SfDiagonalKernel.diagonalFirst A f).hom.app M ≫
      (push A (pullback.fst f f)).map
        ((TraceDiagonalDatum.diagonalIso (Λ := A) f).hom.app M ≫
          (CoordinateTrace.swap A (pullback f f)
            ((push A (TraceDiagonalDatum.diagonal f)).obj
              (derivedTensorUnit (ModuleCat.{u + 1} A) X))
            ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).hom) =
    (unitRightUnitor (ModuleCat.{u + 1} A) X M).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((SfDiagonalKernel.diagonalFirst A f).hom.app
          (derivedTensorUnit (ModuleCat.{u + 1} A) X)) ≫
      (orderedProjection A (pullback.fst f f) M
        ((push A (TraceDiagonalDatum.diagonal f)).obj
          (derivedTensorUnit (ModuleCat.{u + 1} A) X))).hom := by
  exact section_unit_of_isos A (TraceDiagonalDatum.diagonal f) (pullback.fst f f)
    (TraceDiagonalDatum.diagonal_fst f) (SfDiagonalKernel.diagonalFirst A f)
    (sectionPush_first A f) (TraceDiagonalDatum.diagonalIso (Λ := A) f)
    (sectionTensor_first A f) M

-- Assemble with the proof-local category and properness instances fixed.
private theorem insertion_projection_aux {B : DerivedCategoryModule A X}
    (L : DerivedCategoryModule A Y) (e : B ≅ (CoordinateTrace.pull A f).obj L)
    (δ : (push A (TraceDiagonalDatum.diagonal f)).obj
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
      (CoordinateTrace.pull A (pullback.snd f f)).obj B) :
    (∀ M : DerivedCategoryModule A X,
      (push A f).map (insertionApp A f δ M) ≫
          (directComparison A f).hom.app (kernel A f B M) ≫
            (push A f).map
              (orderedProjection A (pullback.fst f f) M
                ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv =
        (push A f).map
          ((unitRightUnitor (ModuleCat.{u + 1} A) X M).inv ≫
            ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              ((SfDiagonalKernel.diagonalFirst A f).hom.app
                  (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
                (push A (pullback.fst f f)).map δ))) ∧
    (∀ K : DerivedCategoryModule A Y,
      insertionApp A f δ ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj
        B).obj K) ≫
          (push A (pullback.snd f f)).map
            (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
              (coordinateTwisted A f L K e).hom).app
                ((CoordinateTrace.pull A (pullback.snd f f)).obj B)) ≫
            (orderedProjection A (pullback.snd f f) ((CoordinateTrace.pull A f ⋙ (derivedTensor
              (ModuleCat.{u + 1} A) X).obj B).obj K)
              ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv =
        (unitRightUnitor (ModuleCat.{u + 1} A) X
            ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
              K)).inv ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
                K)).map
            ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
                (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
              (push A (pullback.snd f f)).map δ)) := by
  let S := push A (TraceDiagonalDatum.diagonal f)
  let P := push A (pullback.fst f f)
  let Q := push A (pullback.snd f f)
  let U := S.obj (derivedTensorUnit (ModuleCat.{u + 1} A) X)
  let E := (CoordinateTrace.pull A (pullback.snd f f)).obj B
  let T := derivedTensor (ModuleCat.{u + 1} A) X
  let TW := derivedTensor (ModuleCat.{u + 1} A) (pullback f f)
  constructor
  · intro M
    exact first_insertion_assembly (push A f) P Q (directComparison A f) (T.obj M)
      ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app M)
      ((SfDiagonalKernel.diagonalFirst A f).hom.app M)
      ((TraceDiagonalDatum.diagonalIso (Λ := A) f).hom.app M ≫
        (CoordinateTrace.swap A (pullback f f) U
          ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).hom)
      ((TW.obj ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).map δ)
      (orderedProjection A (pullback.fst f f) M U)
      (orderedProjection A (pullback.fst f f) M E)
      (unitRightUnitor (ModuleCat.{u + 1} A) X M).inv
      ((SfDiagonalKernel.diagonalFirst A f).hom.app
        (derivedTensorUnit (ModuleCat.{u + 1} A) X)) δ (insertionApp A f δ M)
      (insertionApp_factor A f δ M) (diagonalPushComparison A f M)
      (diagonalFirst_unit A f M)
      (orderedProjection_naturality A (pullback.fst f f) M δ)
  · intro K
    let M := (CoordinateTrace.pull A f ⋙ T.obj B).obj K
    let c := (coordinateTwisted A f L K e).hom
    exact second_insertion_assembly Q (T.obj M)
      ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app M)
      ((TraceDiagonalDatum.diagonalIso (Λ := A) f).hom.app M)
      (CoordinateTrace.swap A (pullback f f) U
        ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).hom
      ((TW.obj ((CoordinateTrace.pull A (pullback.fst f f)).obj M)).map δ)
      ((TW.map c).app E) ((TW.map c).app U)
      ((TW.obj ((CoordinateTrace.pull A (pullback.snd f f)).obj M)).map δ)
      ((properSectionTensorIso A (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
        (TraceDiagonalDatum.diagonal_snd f)).hom.app M ≫
        (CoordinateTrace.swap A (pullback f f) U
          ((CoordinateTrace.pull A (pullback.snd f f)).obj M)).hom)
      (orderedProjection A (pullback.snd f f) M U)
      (orderedProjection A (pullback.snd f f) M E)
      (unitRightUnitor (ModuleCat.{u + 1} A) X M).inv
      ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
        (derivedTensorUnit (ModuleCat.{u + 1} A) X)) δ (insertionApp A f δ M)
      (insertionApp_factor A f δ M) ((TW.map c).naturality δ)
      (diagonal_tensor_second A f (CoordinateTrace.tensor A Y L K)
        (coefficientPull A f L K e))
      (section_unit_of_isos A (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
        (TraceDiagonalDatum.diagonal_snd f)
        (TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f) (sectionPush_second A f)
        (properSectionTensorIso A (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
          (TraceDiagonalDatum.diagonal_snd f)) rfl M)
      (orderedProjection_naturality A (pullback.snd f f) M δ)

end Naturality

/-- Insertion commutes with projection, leaving tensor with the pushed-forward class.
No trace, line condition, or normalized integral is assumed.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the sentences beginning
"Naturality of the tensor projection map" and "Since p1*q*K=p2*q*K"
(auxiliary; not a blueprint node).

Proof: Write U=RDelta!1. Naturality of the projection formula in U->p2*B moves delta
past inverse projection, leaving tensor with Rp_i!(delta). For i=1, use the normalized
composition comparisons for fp1=fp2 to identify F Rp2! RDelta! with F Rp1! RDelta!.
Projection composition and Delta p1=id identify the remaining insertion of U with the
right unitor inverse followed by tensor with diagonalFirst at 1. This gives the first
formula. For i=2 use that M= B tensor f*K is itself pulled back from L tensor K, via e
and coefficientPull. Naturality of these pullback comparisons identifies its coordinate
comparison with coordinateTwisted. On restriction along Delta this comparison is identity,
since both projection composites are identity. Projection composition and Delta p2=id
therefore identify the insertion of U with the right unitor inverse followed by tensor
with idIsoDiagonalSnd at 1, giving the second formula. All symmetries occur in inverse
pairs by the definition of orderedProjection. The argument is natural in an arbitrary
diagonal class; it imposes no trace-exchange equation or diagonal normalization. -/
theorem insertion_projection {B : DerivedCategoryModule A X}
    (L : DerivedCategoryModule A Y) (e : B ≅ (CoordinateTrace.pull A f).obj L)
    (δ : (push A (TraceDiagonalDatum.diagonal f)).obj
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
      (CoordinateTrace.pull A (pullback.snd f f)).obj B) :
    (∀ M : DerivedCategoryModule A X,
      (push A f).map (insertionApp A f δ M) ≫
          (directComparison A f).hom.app (kernel A f B M) ≫
            (push A f).map
              (orderedProjection A (pullback.fst f f) M
                ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv =
        (push A f).map
          ((unitRightUnitor (ModuleCat.{u + 1} A) X M).inv ≫
            ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              ((SfDiagonalKernel.diagonalFirst A f).hom.app
                  (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
                (push A (pullback.fst f f)).map δ))) ∧
    (∀ K : DerivedCategoryModule A Y,
      insertionApp A f δ ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj
        B).obj K) ≫
          (push A (pullback.snd f f)).map
            (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
              (coordinateTwisted A f L K e).hom).app
                ((CoordinateTrace.pull A (pullback.snd f f)).obj B)) ≫
            (orderedProjection A (pullback.snd f f) ((CoordinateTrace.pull A f ⋙ (derivedTensor
              (ModuleCat.{u + 1} A) X).obj B).obj K)
              ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv =
        (unitRightUnitor (ModuleCat.{u + 1} A) X
            ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
              K)).inv ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
                K)).map
            ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
                (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
              (push A (pullback.snd f f)).map δ)) := by
  exact insertion_projection_aux A f L e δ

end AlgebraicGeometry.Etale.SupportedTrace
