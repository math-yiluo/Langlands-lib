/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import WeilConjectures.AlgebraicGeometry.SfSupportedCoefficientBraid
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # Second coordinate extraction before a trace

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, second triangle, common coefficient extraction.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open MonoidalCategory BraidedCategory

open MonoidalCategory BraidedCategory in
private theorem cyclic_projection
    {D W : Type*} [Category D] [Category W]
    [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalCategory W] [BraidedCategory W]
    (V : D ⥤ W) (P : W ⥤ D)
    (δ : ∀ K B : D, V.obj (K ⊗ B) ≅ V.obj K ⊗ V.obj B)
    (p : ∀ (E : W) (K : D), P.obj E ⊗ K ≅ P.obj (E ⊗ V.obj K))
    (ha : ∀ E K B,
      (p E K).hom ▷ B ≫ (p (E ⊗ V.obj K) B).hom ≫
          P.map (α_ E (V.obj K) (V.obj B)).hom =
        (α_ (P.obj E) K B).hom ≫ (p E (K ⊗ B)).hom ≫
          P.map (E ◁ (δ K B).hom))
    (hn : ∀ E K B,
      P.obj E ◁ (β_ K B).hom ≫ (p E (B ⊗ K)).hom =
        (p E (K ⊗ B)).hom ≫ P.map (E ◁ V.map (β_ K B).hom))
    (hb : ∀ K B,
      V.map (β_ K B).hom ≫ (δ B K).hom =
        (δ K B).hom ≫ (β_ (V.obj K) (V.obj B)).hom)
    (E : W) (K B : D) :
    (p (E ⊗ V.obj K) B).inv ≫ (p E K).inv ▷ B ≫
        (β_ (P.obj E ⊗ K) B).hom =
      P.map (α_ E (V.obj K) (V.obj B)).hom ≫
        P.map (E ◁ (β_ (V.obj K) (V.obj B)).hom) ≫
        P.map (E ◁ (δ B K).inv) ≫ (p E (B ⊗ K)).inv ≫
        (β_ (P.obj E) (B ⊗ K)).hom ≫ (α_ B K (P.obj E)).hom ≫
        B ◁ (β_ K (P.obj E)).hom := by
  have hi : (p (E ⊗ V.obj K) B).inv ≫ (p E K).inv ▷ B =
      P.map (α_ E (V.obj K) (V.obj B)).hom ≫
        P.map (E ◁ (δ K B).inv) ≫ (p E (K ⊗ B)).inv ≫
        (α_ (P.obj E) K B).inv := by
    have he : whiskerRightIso (p E K) B ≪≫ p (E ⊗ V.obj K) B =
        α_ (P.obj E) K B ≪≫ p E (K ⊗ B) ≪≫
          P.mapIso (whiskerLeftIso E (δ K B)) ≪≫
          (P.mapIso (α_ E (V.obj K) (V.obj B))).symm := by
      apply Iso.ext
      change (p E K).hom ▷ B ≫ (p (E ⊗ V.obj K) B).hom =
        (α_ (P.obj E) K B).hom ≫ (p E (K ⊗ B)).hom ≫
          P.map (E ◁ (δ K B).hom) ≫ P.map (α_ E (V.obj K) (V.obj B)).inv
      rw [← reassoc_of% (ha E K B), ← P.map_comp, Iso.hom_inv_id,
        P.map_id, Category.comp_id]
    have he' := congrArg Iso.inv he
    simpa only [Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
      CategoryTheory.Functor.mapIso_hom, Iso.symm_inv,
      whiskerRightIso_inv, whiskerLeftIso_inv, Category.assoc] using he'
  have hbi : (β_ (V.obj K) (V.obj B)).hom ≫ (δ B K).inv =
      (δ K B).inv ≫ V.map (β_ K B).hom := by
    apply (cancel_epi (δ K B).hom).1
    rw [← Category.assoc, ← hb]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hni : P.map (E ◁ V.map (β_ K B).hom) ≫ (p E (B ⊗ K)).inv =
      (p E (K ⊗ B)).inv ≫ P.obj E ◁ (β_ K B).hom := by
    apply (cancel_epi (p E (K ⊗ B)).hom).1
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hc : (α_ (P.obj E) K B).inv ≫ (β_ (P.obj E ⊗ K) B).hom =
      P.obj E ◁ (β_ K B).hom ≫ (β_ (P.obj E) (B ⊗ K)).hom ≫
        (α_ B K (P.obj E)).hom ≫ B ◁ (β_ K (P.obj E)).hom := by
    simp only [braiding_tensor_left_hom, braiding_tensor_right_hom,
      Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp,
      SymmetricCategory.symmetry, whiskerLeft_id, Category.comp_id]
  rw [reassoc_of% hi]
  rw [hc]
  have hm : P.map (E ◁ (β_ (V.obj K) (V.obj B)).hom) ≫
      P.map (E ◁ (δ B K).inv) =
    P.map (E ◁ (δ K B).inv) ≫ P.map (E ◁ V.map (β_ K B).hom) := by
    rw [← P.map_comp, ← whiskerLeft_comp, hbi, whiskerLeft_comp, P.map_comp]
  rw [reassoc_of% hm, reassoc_of% hni]

open MonoidalCategory BraidedCategory in
private theorem second_extraction_formal
    {D W : Type*} [Category D] [Category W]
    [MonoidalCategory D] [BraidedCategory D] [MonoidalCategory W]
    (V : D ⥤ W) (P : W ⥤ D) (B Q : D)
    {T S H : D} {R E : W} (a : P.obj R ⟶ T) (q : T ⟶ H)
    (b : P.obj E ⟶ S) (δ : H ≅ S ⊗ Q)
    (d : R ≅ E ⊗ V.obj Q)
    (z : (E ⊗ V.obj Q) ⊗ V.obj B ≅ V.obj (B ⊗ Q) ⊗ E)
    (cM : R ≅ V.obj (B ⊗ Q)) (cB : E ≅ V.obj B)
    (p0 : P.obj R ⊗ B ≅ P.obj (R ⊗ V.obj B))
    (p1 : P.obj E ⊗ Q ≅ P.obj (E ⊗ V.obj Q))
    (p2 : P.obj (E ⊗ V.obj Q) ⊗ B ≅ P.obj ((E ⊗ V.obj Q) ⊗ V.obj B))
    (o : (B ⊗ Q) ⊗ P.obj E ≅ P.obj (V.obj (B ⊗ Q) ⊗ E))
    (o' : (B ⊗ Q) ⊗ P.obj (V.obj B) ≅ P.obj (V.obj (B ⊗ Q) ⊗ V.obj B))
    (s : (B ⊗ Q) ⊗ S ≅ B ⊗ H) (C : P.obj (R ⊗ V.obj B) ⟶ B ⊗ T)
    (hC : C = p0.inv ≫ a ▷ B ≫ (β_ T B).hom)
    (hx : a ≫ q = P.map d.hom ≫ p1.inv ≫ b ▷ Q ≫ δ.inv)
    (hd : p0.inv ≫ P.map d.hom ▷ B = P.map (d.hom ▷ V.obj B) ≫ p2.inv)
    (hc : P.map (d.hom ▷ V.obj B) ≫ P.map z.hom =
      P.map (cM.hom ▷ V.obj B) ≫ P.map (V.obj (B ⊗ Q) ◁ cB.inv))
    (hn : P.map (V.obj (B ⊗ Q) ◁ cB.inv) ≫ o.inv =
      o'.inv ≫ (B ⊗ Q) ◁ P.map cB.inv)
    (ht : (α_ B Q (P.obj E)).hom ≫ B ◁ (β_ Q (P.obj E)).hom ≫
      B ◁ (b ▷ Q ≫ δ.inv) = (B ⊗ Q) ◁ b ≫ s.hom)
    (hcyc : p2.inv ≫ p1.inv ▷ B ≫ (β_ (P.obj E ⊗ Q) B).hom =
      P.map z.hom ≫ o.inv ≫ (α_ B Q (P.obj E)).hom ≫ B ◁ (β_ Q (P.obj E)).hom) :
    C ≫ B ◁ q = P.map (cM.hom ▷ V.obj B) ≫ o'.inv ≫
      (B ⊗ Q) ◁ (P.map cB.inv ≫ b) ≫ s.hom := by
  calc
    _ = p0.inv ≫ (a ≫ q) ▷ B ≫ (β_ H B).hom := by
      rw [hC, Category.assoc, Category.assoc, ← braiding_naturality_left,
        ← comp_whiskerRight_assoc]
    _ = p0.inv ≫ P.map d.hom ▷ B ≫ p1.inv ▷ B ≫
        (β_ (P.obj E ⊗ Q) B).hom ≫ B ◁ (b ▷ Q ≫ δ.inv) := by
      rw [hx]
      simp only [comp_whiskerRight, Category.assoc]
      rw [braiding_naturality_left, braiding_naturality_left_assoc]
      simp only [whiskerLeft_comp]
    _ = P.map (d.hom ▷ V.obj B) ≫ p2.inv ≫ p1.inv ▷ B ≫
        (β_ (P.obj E ⊗ Q) B).hom ≫ B ◁ (b ▷ Q ≫ δ.inv) := by
      rw [reassoc_of% hd]
    _ = P.map (d.hom ▷ V.obj B) ≫ P.map z.hom ≫ o.inv ≫
        (α_ B Q (P.obj E)).hom ≫ B ◁ (β_ Q (P.obj E)).hom ≫
        B ◁ (b ▷ Q ≫ δ.inv) := by
      rw [reassoc_of% hcyc]
    _ = P.map (cM.hom ▷ V.obj B) ≫ o'.inv ≫
        (B ⊗ Q) ◁ (P.map cB.inv ≫ b) ≫ s.hom := by
      rw [ht, reassoc_of% hc, reassoc_of% hn, whiskerLeft_comp, Category.assoc]

open MonoidalCategory BraidedCategory in
private theorem shuffle_transport
    {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]
    (B Q : D) {E S H : D} (b : E ⟶ S) (δ : H ≅ S ⊗ Q) :
    (α_ B Q E).hom ≫ B ◁ (β_ Q E).hom ≫ B ◁ (b ▷ Q ≫ δ.inv) =
      (B ⊗ Q) ◁ b ≫ (α_ B Q S).hom ≫ B ◁ (β_ Q S).hom ≫ B ◁ δ.inv := by
  rw [whiskerLeft_comp, ← whiskerLeft_comp_assoc,
    ← braiding_naturality_right, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← associator_naturality_right_assoc]

private theorem inverse_square
    {D : Type*} [Category D] {H X Y Z W : D}
    (a : H ≅ X) (d : X ≅ Y) (q : Z ≅ Y) (t : W ≅ Z) (δ : H ≅ W)
    (h : a.hom ≫ d.hom = δ.hom ≫ t.hom ≫ q.hom) :
    a.inv = d.hom ≫ q.inv ≫ t.inv ≫ δ.inv := by
  apply (cancel_epi a.hom).1
  rw [reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id]

namespace AlgebraicGeometry.Etale.SupportedTrace

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

section GeneralCoefficients

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]

/-- Reassociate and swap the two base coefficients, then undo tensor pullback.
Source: thm-amb-p1-adjunction.proof.md, second triangle before the scalar trace
(auxiliary; not a blueprint node). -/
def extractionShuffle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (N K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    ((derivedTensor C X).obj
        (((derivedTensor C X).obj B).obj ((upperStar C f).leftDerivedFunctor.obj K))).obj
          ((upperStar C f).leftDerivedFunctor.obj N) ≅
      ((derivedTensor C X).obj B).obj
        ((upperStar C f).leftDerivedFunctor.obj (((derivedTensor C Y).obj N).obj K)) :=
  derivedTensorAssociator C X B ((upperStar C f).leftDerivedFunctor.obj K)
      ((upperStar C f).leftDerivedFunctor.obj N) ≪≫
    ((derivedTensor C X).obj B).mapIso
      (((derivedTensorSymmetry C X).app ((upperStar C f).leftDerivedFunctor.obj K)).app
        ((upperStar C f).leftDerivedFunctor.obj N)) ≪≫
    ((derivedTensor C X).obj B).mapIso (leftDerivedUpperStarTensorIso C f N K).symm

omit [UpperStarPreservesFlat C] in
private theorem swap_inverse_hom {X : Scheme.{u}}
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (((derivedTensorSymmetry C X).app M).app N).inv =
      (letI := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology C)
       (β_ N M).hom) := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology C)
  change (β_ M N).inv = (β_ N M).hom
  exact (SymmetricCategory.braiding_swap_eq_inv_braiding M N).symm

omit [UpperStarPreservesFlat C] in
private theorem tensor_right_map {X : Scheme.{u}}
    {M M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)} (v : M ⟶ M')
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (derivedTensorRight C X N).map v = v ▷ N := rfl

omit [UpperStarPreservesFlat C] in
private theorem swap_forward_hom {X : Scheme.{u}}
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (((derivedTensorSymmetry C X).app M).app N).hom =
      (letI := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology C)
       (β_ M N).hom) := by
  rfl

omit [UpperStarPreservesFlat C] in
private theorem associator_forward_hom {X : Scheme.{u}}
    (M N T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (derivedTensorAssociator C X M N T).hom = (α_ M N T).hom := by
  rfl

open MonoidalCategory BraidedCategory in
private theorem extraction_shuffle_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (N K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (extractionShuffle C f B N K).hom =
      (letI := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology C)
       (α_ B ((upperStar C f).leftDerivedFunctor.obj K)
          ((upperStar C f).leftDerivedFunctor.obj N)).hom ≫
        B ◁ (β_ ((upperStar C f).leftDerivedFunctor.obj K)
          ((upperStar C f).leftDerivedFunctor.obj N)).hom ≫
        B ◁ (leftDerivedUpperStarTensorIso C f N K).inv) := by
  rfl

open MonoidalCategory BraidedCategory in
private theorem projection_cycle_generic {Z X : Scheme.{u}} (g : Z ⟶ X)
    (P : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (π : ∀ E, (derivedTensor C X).obj (P.obj E) ≅
      (upperStar C g).leftDerivedFunctor ⋙ (derivedTensor C Z).obj E ⋙ P)
    (ha : ∀ E Q N,
      ((π E).app Q).hom ▷ N ≫
          ((π (E ⊗ (upperStar C g).leftDerivedFunctor.obj Q)).app N).hom ≫
          P.map (α_ E ((upperStar C g).leftDerivedFunctor.obj Q)
            ((upperStar C g).leftDerivedFunctor.obj N)).hom =
        (α_ (P.obj E) Q N).hom ≫ ((π E).app (Q ⊗ N)).hom ≫
          P.map (E ◁ (leftDerivedUpperStarTensorIso C g Q N).hom))
    (E : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (Q N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (π (((derivedTensor C Z).obj E).obj
        ((upperStar C g).leftDerivedFunctor.obj Q))).inv.app N ≫
        ((derivedTensor C X).map ((π E).inv.app Q)).app N ≫
        (((derivedTensorSymmetry C X).app
          (((derivedTensor C X).obj (P.obj E)).obj Q)).app N).hom =
      P.map (cyclicShuffle C g E N Q).hom ≫
        ((((derivedTensorSymmetry C X).app
          (((derivedTensor C X).obj N).obj Q)).app (P.obj E)) ≪≫
          (π E).app (((derivedTensor C X).obj N).obj Q) ≪≫
          P.mapIso (((derivedTensorSymmetry C Z).app E).app
            ((upperStar C g).leftDerivedFunctor.obj
              (((derivedTensor C X).obj N).obj Q)))).inv ≫
        (derivedTensorAssociator C X N Q (P.obj E)).hom ≫
        ((derivedTensor C X).obj N).map
          (((derivedTensorSymmetry C X).app Q).app (P.obj E)).hom := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology C)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Z.smallEtaleTopology C)
  let V := (upperStar C g).leftDerivedFunctor
  let δ : ∀ Q N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      V.obj (Q ⊗ N) ≅ V.obj Q ⊗ V.obj N := leftDerivedUpperStarTensorIso C g
  let p : ∀ (E : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C))
      (Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)),
      P.obj E ⊗ Q ≅ P.obj (E ⊗ V.obj Q) := fun E Q ↦ (π E).app Q
  have hn : ∀ E Q N,
      P.obj E ◁ (β_ Q N).hom ≫ (p E (N ⊗ Q)).hom =
        (p E (Q ⊗ N)).hom ≫ P.map (E ◁ V.map (β_ Q N).hom) := by
    intro E Q N
    exact (π E).hom.naturality (β_ Q N).hom
  have hb : ∀ Q N,
      V.map (β_ Q N).hom ≫ (δ N Q).hom =
        (δ Q N).hom ≫ (β_ (V.obj Q) (V.obj N)).hom := by
    intro Q N
    have h := leftDerivedUpperStar_map_braiding_hom_δ C g Q N
    rw [leftDerivedUpperStar_δ_eq] at h
    change V.map (β_ Q N).hom ≫ (δ N Q).hom =
      (δ Q N).hom ≫ (β_ (V.obj Q) (V.obj N)).hom at h
    exact h
  have h := cyclic_projection V P δ p ha hn hb E Q N
  change (p (E ⊗ V.obj Q) N).inv ≫ (p E Q).inv ▷ N ≫
      (β_ (P.obj E ⊗ Q) N).hom = _
  rw [h]
  simp only [cyclicShuffle, Iso.trans_hom, Iso.trans_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    Iso.symm_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  change _ = P.map (α_ E (V.obj Q) (V.obj N)).hom ≫
    P.map (E ◁ (β_ (V.obj Q) (V.obj N)).hom) ≫
    P.map (E ◁ (δ N Q).inv) ≫ P.map (β_ E (V.obj (N ⊗ Q))).hom ≫
    P.map (β_ E (V.obj (N ⊗ Q))).inv ≫ (p E (N ⊗ Q)).inv ≫
    (β_ (N ⊗ Q) (P.obj E)).inv ≫ (α_ N Q (P.obj E)).hom ≫
    N ◁ (β_ Q (P.obj E)).hom
  have hp : P.map (β_ E (V.obj (N ⊗ Q))).hom ≫
      P.map (β_ E (V.obj (N ⊗ Q))).inv = 𝟙 _ := by
    rw [← P.map_comp, Iso.hom_inv_id, P.map_id]
  rw [reassoc_of% hp]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding (N ⊗ Q) (P.obj E)]

omit [UpperStarPreservesFlat C] in
private theorem ordered_inverse_naturality_generic {Z X : Scheme.{u}} (g : Z ⟶ X)
    (P : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (q : ∀ E : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C),
      P.obj E ⊗ M ≅ P.obj (E ⊗ (upperStar C g).leftDerivedFunctor.obj M))
    (hn : ∀ {E E'} (v : E ⟶ E'),
      P.map (v ▷ (upperStar C g).leftDerivedFunctor.obj M) ≫ (q E').inv =
        (q E).inv ≫ P.map v ▷ M)
    {E E' : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)} (v : E ⟶ E') :
    P.map (((derivedTensor C Z).obj
        ((upperStar C g).leftDerivedFunctor.obj M)).map v) ≫
        ((((derivedTensorSymmetry C X).app M).app (P.obj E')) ≪≫ q E' ≪≫
          P.mapIso (((derivedTensorSymmetry C Z).app E').app
            ((upperStar C g).leftDerivedFunctor.obj M))).inv =
      ((((derivedTensorSymmetry C X).app M).app (P.obj E)) ≪≫ q E ≪≫
          P.mapIso (((derivedTensorSymmetry C Z).app E).app
            ((upperStar C g).leftDerivedFunctor.obj M))).inv ≫
        ((derivedTensor C X).obj M).map (P.map v) := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology C)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Z.smallEtaleTopology C)
  let V := (upperStar C g).leftDerivedFunctor
  simp only [Iso.trans_inv, CategoryTheory.Functor.mapIso_inv, Category.assoc]
  change P.map (V.obj M ◁ v) ≫ P.map (β_ E' (V.obj M)).inv ≫
      (q E').inv ≫ (β_ M (P.obj E')).inv =
    P.map (β_ E (V.obj M)).inv ≫ (q E).inv ≫
      (β_ M (P.obj E)).inv ≫ M ◁ P.map v
  rw [← P.map_comp_assoc, braiding_inv_naturality_right, P.map_comp,
    Category.assoc, reassoc_of% (hn v), braiding_inv_naturality_left]

private theorem inverse_exchange_generic {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (P : _root_.DerivedCategory (Sheaf (pullback f f).smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (β : F ⋙ (upperStar C f).leftDerivedFunctor ≅
      (upperStar C (pullback.fst f f)).leftDerivedFunctor ⋙ P)
    (πf : ∀ E, (derivedTensor C Y).obj (F.obj E) ≅
      (upperStar C f).leftDerivedFunctor ⋙ (derivedTensor C X).obj E ⋙ F)
    (πp : ∀ E, (derivedTensor C X).obj (P.obj E) ≅
      (upperStar C (pullback.snd f f)).leftDerivedFunctor ⋙
        (derivedTensor C (pullback f f)).obj E ⋙ P)
    (B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (h : (upperStar C f).leftDerivedFunctor.map ((πf B).hom.app K) ≫
        β.hom.app (((derivedTensor C X).obj B).obj
          ((upperStar C f).leftDerivedFunctor.obj K)) ≫
        P.map (((leftDerivedUpperStarTensorComparison C (pullback.fst f f)).app B).app
          ((upperStar C f).leftDerivedFunctor.obj K)) ≫
        P.map (((derivedTensor C (pullback f f)).obj
          ((upperStar C (pullback.fst f f)).leftDerivedFunctor.obj B)).map
            (derivedSquareUpperStarIsoInvApp C
              (IsPullback.of_hasPullback f f).toCommSq K)) =
      ((leftDerivedUpperStarTensorComparison C f).app (F.obj B)).app K ≫
        ((derivedTensor C X).map (β.hom.app B)).app
          ((upperStar C f).leftDerivedFunctor.obj K) ≫
        (πp ((upperStar C (pullback.fst f f)).leftDerivedFunctor.obj B)).hom.app
          ((upperStar C f).leftDerivedFunctor.obj K)) :
    β.inv.app (((derivedTensor C X).obj B).obj
        ((upperStar C f).leftDerivedFunctor.obj K)) ≫
        (upperStar C f).leftDerivedFunctor.map ((πf B).inv.app K) =
      P.map (coefficientSplit C f B K).hom ≫
        (πp ((upperStar C (pullback.fst f f)).leftDerivedFunctor.obj B)).inv.app
          ((upperStar C f).leftDerivedFunctor.obj K) ≫
        ((derivedTensor C X).map (β.inv.app B)).app
          ((upperStar C f).leftDerivedFunctor.obj K) ≫
        (leftDerivedUpperStarTensorIso C f (F.obj B) K).inv := by
  let U := (upperStar C f).leftDerivedFunctor
  let R := (upperStar C (pullback.fst f f)).leftDerivedFunctor
  let M := ((derivedTensor C X).obj B).obj (U.obj K)
  let a := U.mapIso ((πf B).app K) ≪≫ β.app M
  let t := ((derivedTensor C X).mapIso (β.app B)).app (U.obj K)
  let q := (πp (R.obj B)).app (U.obj K)
  let d := coefficientSplit C f B K
  let δ := leftDerivedUpperStarTensorIso C f (F.obj B) K
  have he : a.hom ≫ P.map d.hom = δ.hom ≫ t.hom ≫ q.hom := by
    simpa only [a, t, q, d, δ, coefficientSplit, Iso.trans_hom, Iso.app_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
      derivedSquareUpperStarIsoInvApp, CategoryTheory.Functor.map_comp, Category.assoc,
      leftDerivedUpperStarTensorIso_hom, U, R, M] using h
  have hi := inverse_square a (P.mapIso d) q t δ he
  simpa only [a, t, q, δ, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
    CategoryTheory.Functor.mapIso_hom, Iso.app_inv] using hi

end GeneralCoefficients

variable (A : Type (u + 1)) [CommRing A] [Finite A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

open MonoidalCategory BraidedCategory in
private theorem projection_cycle {Z X : Scheme.{u}} (g : Z ⟶ X)
    [HasCompactification g]
    (E : DerivedCategoryModule A Z) (Q N : DerivedCategoryModule A X) :
    (projectionIso A g
        (((derivedTensor (ModuleCat.{u + 1} A) Z).obj E).obj
          ((CoordinateTrace.pull A g).obj Q))).inv.app N ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((projectionIso A g E).inv.app Q)).app N ≫
        (CoordinateTrace.swap A X
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj ((push A g).obj E)).obj Q) N).hom =
      (push A g).map (cyclicShuffle (ModuleCat.{u + 1} A) g E N Q).hom ≫
        (orderedProjection A g
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj N).obj Q) E).inv ≫
        (derivedTensorAssociator (ModuleCat.{u + 1} A) X N Q ((push A g).obj E)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj N).map
          (CoordinateTrace.swap A X Q ((push A g).obj E)).hom := by
  have h := projection_cycle_generic (ModuleCat.{u + 1} A) g (push A g)
    (projectionIso A g) (fun E Q N ↦ (projectionMapAssociativity A g).assoc E Q N) E Q N
  exact h

private theorem projection_right_app {Z X : Scheme.{u}} (g : Z ⟶ X)
    [HasCompactification g] (E : DerivedCategoryModule A Z)
    (M : DerivedCategoryModule A X) :
    (projectionRightIso A g M).app E = (projectionIso A g E).app M := by
  apply Iso.ext
  rfl

attribute [local irreducible] projectionIso projectionRightIso
  TraceDiagonalDatum.baseChangeIso

open MonoidalCategory in
private theorem projection_inverse_naturality {Z X : Scheme.{u}} (g : Z ⟶ X)
    [HasCompactification g] (M : DerivedCategoryModule A X)
    {E E' : DerivedCategoryModule A Z} (v : E ⟶ E') :
    (push A g).map (v ▷ (CoordinateTrace.pull A g).obj M) ≫
        (projectionIso A g E').inv.app M =
      (projectionIso A g E).inv.app M ≫ (push A g).map v ▷ M := by
  have hn := (projectionRightIso A g M).inv.naturality v
  simp only [← Iso.app_inv, projection_right_app] at hn
  change (push A g).map (v ▷ (CoordinateTrace.pull A g).obj M) ≫
      (projectionIso A g E').inv.app M =
    (projectionIso A g E).inv.app M ≫ (push A g).map v ▷ M at hn
  exact hn

open MonoidalCategory BraidedCategory in
private theorem ordered_inverse_naturality {Z X : Scheme.{u}} (g : Z ⟶ X)
    [HasCompactification g] (M : DerivedCategoryModule A X)
    {E E' : DerivedCategoryModule A Z} (v : E ⟶ E') :
    (push A g).map
        (((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          ((CoordinateTrace.pull A g).obj M)).map v) ≫
        (orderedProjection A g M E').inv =
      (orderedProjection A g M E).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map ((push A g).map v) := by
  exact ordered_inverse_naturality_generic (ModuleCat.{u + 1} A) g (push A g) M
    (fun E ↦ (projectionIso A g E).app M)
    (fun v ↦ projection_inverse_naturality A g M v) v

private theorem inverse_exchange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
          ((CoordinateTrace.pull A f).obj K)) ≫
        (CoordinateTrace.pull A f).map ((projectionIso A f B).inv.app K) =
      (push A (pullback.snd f f)).map
          (coefficientSplit (ModuleCat.{u + 1} A) f B K).hom ≫
        (projectionIso A (pullback.snd f f)
          ((CoordinateTrace.pull A (pullback.fst f f)).obj B)).inv.app
            ((CoordinateTrace.pull A f).obj K) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app B)).app
            ((CoordinateTrace.pull A f).obj K) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
          ((push A f).obj B) K).inv := by
  apply inverse_exchange_generic (ModuleCat.{u + 1} A) f (push A f)
    (push A (pullback.snd f f)) (TraceDiagonalDatum.baseChangeIso (Λ := A) f)
    (projectionIso A f) (projectionIso A (pullback.snd f f)) B K
  have h := projectionMap_rightDerivedLowerShriekBaseChangeMap A
    (IsPullback.of_hasPullback f f) B K
  simpa only [TraceDiagonalDatum.baseChangeIso, projectionIso, asIso_hom] using h

private theorem comparison_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (B M : DerivedCategoryModule A X) :
    (comparison A f B M).hom =
      (projectionRightIso A (pullback.snd f f) B).inv.app
          ((CoordinateTrace.pull A (pullback.fst f f)).obj M) ≫
        (derivedTensorRight (ModuleCat.{u + 1} A) X B).map
          ((TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app M) ≫
        (CoordinateTrace.swap A X B
          ((CoordinateTrace.pull A f).obj ((push A f).obj M))).inv := by
  simp only [comparison, comparisonIso, TraceDiagonalDatum.sndProjectionIso,
    Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, CoordinateTrace.swap, Iso.app_inv]

/-- The second-coordinate isomorphism calculation before a scalar trace is applied.
Source: thm-amb-p1-adjunction.proof.md, second triangle, extraction of the common
coefficient and the even self-symmetry (auxiliary; not a blueprint node).

Proof: use exchange/projection compatibility for the canonical self-product square
and invert the resulting square. Tensor with B and apply projection associativity.
Transport e through the tensor pullback comparisons. The two copies of the line
on the product can be exchanged without changing the map, by the hypothesis on
its canonical self-symmetry and the braided pullback comparisons. The comparison
on the entire coefficient B tensor f*K is then exactly coordinateTwisted. The
remaining operations are inverse second-coordinate exchange, inverse coordinate
comparison on B and the reassociation extractionShuffle. This proves the identity
of maps to B tensor f*(Rf!B tensor K), before a trace Rf!B -> A is chosen.
The native compact-support projection/exchange square supplies this compatibility
directly; all compositors and exchanges remain canonical.
No trace, diagonal class, integral normalization or triangle identity occurs. -/
theorem secondExtraction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y)
    (hL : (CoordinateTrace.swap A Y L L).hom = 𝟙 _)
    {B : DerivedCategoryModule A X} (e : B ≅ (CoordinateTrace.pull A f).obj L)
    (K : DerivedCategoryModule A Y) :
    (comparison A f B
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
          ((CoordinateTrace.pull A f).obj K))).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj B).map
          ((CoordinateTrace.pull A f).map ((projectionIso A f B).inv.app K)) =
      (push A (pullback.snd f f)).map
          (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
            (coordinateTwisted A f L K e).hom).app
              ((CoordinateTrace.pull A (pullback.snd f f)).obj B)) ≫
        (orderedProjection A (pullback.snd f f)
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
            ((CoordinateTrace.pull A f).obj K))
          ((CoordinateTrace.pull A (pullback.snd f f)).obj B)).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
            ((CoordinateTrace.pull A f).obj K))).map
          ((push A (pullback.snd f f)).map (SfDiagonalKernel.coordinate A f L e).inv ≫
            (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app B) ≫
        (extractionShuffle (ModuleCat.{u + 1} A) f B ((push A f).obj B) K).hom := by
  let := _root_.DerivedCategory.symmetricCategory'
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := _root_.DerivedCategory.braidedCategory'
    (Sheaf (pullback f f).smallEtaleTopology (ModuleCat.{u + 1} A))
  let U := CoordinateTrace.pull A f
  let V := CoordinateTrace.pull A (pullback.snd f f)
  let R := CoordinateTrace.pull A (pullback.fst f f)
  let P := push A (pullback.snd f f)
  let Q := U.obj K
  let M := B ⊗ Q
  let E := R.obj B
  let b := (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app B
  let a := (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app M
  let q := U.map ((projectionIso A f B).inv.app K)
  let d : R.obj M ≅ E ⊗ V.obj Q :=
    coefficientSplit (ModuleCat.{u + 1} A) f B K
  let z : (E ⊗ V.obj Q) ⊗ V.obj B ≅ V.obj M ⊗ E :=
    cyclicShuffle (ModuleCat.{u + 1} A) (pullback.snd f f) E B Q
  let δ := leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f ((push A f).obj B) K
  let p : ∀ (E : DerivedCategoryModule A (pullback f f))
      (N : DerivedCategoryModule A X), P.obj E ⊗ N ≅ P.obj (E ⊗ V.obj N) :=
    fun E N ↦ (projectionIso A (pullback.snd f f) E).app N
  let cB : E ≅ V.obj B := SfDiagonalKernel.coordinate A f L e
  let cM : R.obj M ≅ V.obj M := coordinateTwisted A f L K e
  let o := orderedProjection A (pullback.snd f f) M E
  let o' := orderedProjection A (pullback.snd f f) M (V.obj B)
  let s := extractionShuffle (ModuleCat.{u + 1} A) f B ((push A f).obj B) K
  have hC : (comparison A f B M).hom =
      (p (R.obj M) B).inv ≫ a ▷ B ≫ (β_ (U.obj ((push A f).obj M)) B).hom := by
    rw [comparison_hom]
    simp only [← Iso.app_inv, projection_right_app, CoordinateTrace.swap,
      swap_inverse_hom, tensor_right_map]
    simp only [p, a, R, U, Iso.app_inv]
  have hx : a ≫ q = P.map d.hom ≫ (p E Q).inv ≫ b ▷ Q ≫ δ.inv :=
    inverse_exchange A f B K
  have hd : (p (R.obj M) B).inv ≫ P.map d.hom ▷ B =
      P.map (d.hom ▷ V.obj B) ≫ (p (E ⊗ V.obj Q) B).inv := by
    exact (projection_inverse_naturality A (pullback.snd f f) B d.hom).symm
  have hc : P.map (d.hom ▷ V.obj B) ≫ P.map z.hom =
      P.map (cM.hom ▷ V.obj B) ≫ P.map (V.obj M ◁ cB.inv) := by
    have h := congrArg (fun i ↦ P.map i.hom) (coefficientBraid A f L hL e K)
    simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
      CategoryTheory.Functor.map_comp, Iso.app_hom, Iso.symm_hom] at h
    change P.map (d.hom ▷ V.obj B) ≫ P.map z.hom =
      P.map (cM.hom ▷ V.obj B) ≫ P.map (V.obj M ◁ cB.inv) at h
    exact h
  have hn : P.map (V.obj M ◁ cB.inv) ≫ o.inv =
      o'.inv ≫ M ◁ P.map cB.inv :=
    ordered_inverse_naturality A (pullback.snd f f) M cB.inv
  have ht : (α_ B Q (P.obj E)).hom ≫ B ◁ (β_ Q (P.obj E)).hom ≫
      B ◁ (b ▷ Q ≫ δ.inv) = M ◁ b ≫ s.hom := by
    rw [extraction_shuffle_hom (ModuleCat.{u + 1} A) f B ((push A f).obj B) K]
    exact shuffle_transport B Q b δ
  change (comparison A f B M).hom ≫ B ◁ q =
    P.map (cM.hom ▷ V.obj B) ≫ o'.inv ≫ M ◁ (P.map cB.inv ≫ b) ≫ s.hom
  exact second_extraction_formal V P B Q a q b δ d z cM cB
    (p (R.obj M) B) (p E Q) (p (E ⊗ V.obj Q) B) o o' s
    (comparison A f B M).hom hC hx hd hc hn ht
    (by
      have h := projection_cycle A (pullback.snd f f) E Q B
      simpa only [p, E, R, U, V, P, Q, z, o, CoordinateTrace.swap,
        ← Iso.app_inv, CategoryTheory.Functor.comp_obj, derivedTensor,
        curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
        swap_forward_hom, associator_forward_hom] using h)

end AlgebraicGeometry.Etale.SupportedTrace
