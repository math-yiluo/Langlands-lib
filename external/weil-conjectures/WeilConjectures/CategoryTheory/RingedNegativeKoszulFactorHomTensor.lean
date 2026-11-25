/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedNegativeKoszulTransitions
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedKoszulDualizable

/-! # Tensor-Hom comparison for one two-term Koszul factor

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, finite free dual identification.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open MonoidalCategory MonoidalClosed

private structure IsoWithHom {B : Type*} [Category B] {X Y : B} (f : X ⟶ Y) where
  iso : X ≅ Y
  hom_eq : iso.hom = f

private def bifunctorMapIsoData {B : Type*} [Category B] (F : B → B → B)
    (map : ∀ {A A' T T' : B}, (A' ⟶ A) → (T ⟶ T') → (F A T ⟶ F A' T'))
    (hid : ∀ A T, map (𝟙 A) (𝟙 T) = 𝟙 (F A T))
    (hcomp : ∀ {A A' A'' T T' T'' : B} (f : A' ⟶ A) (f' : A'' ⟶ A')
      (g : T ⟶ T') (g' : T' ⟶ T''),
      map f g ≫ map f' g' = map (f' ≫ f) (g ≫ g'))
    {A T U : B} (e : A ≅ U) (s : T ≅ U) (v : F U U ≅ U) :
    IsoWithHom (map e.inv s.hom ≫ v.hom) := by
  let q : F A T ≅ F U U :=
    { hom := map e.inv s.hom
      inv := map e.hom s.inv
      hom_inv_id := by simp only [hcomp, Iso.hom_inv_id, hid]
      inv_hom_id := by simp only [hcomp, Iso.inv_hom_id, hid] }
  exact ⟨q ≪≫ v, rfl⟩

private lemma bifunctorMapEval_natural {B : Type*} [Category B] (F : B → B → B)
    (map : ∀ {A A' T T' : B}, (A' ⟶ A) → (T ⟶ T') → (F A T ⟶ F A' T'))
    (hcomp : ∀ {A A' A'' T T' T'' : B} (f : A' ⟶ A) (f' : A'' ⟶ A')
      (g : T ⟶ T') (g' : T' ⟶ T''),
      map f g ≫ map f' g' = map (f' ≫ f) (g ≫ g'))
    {A A' T U : B} (f : A' ⟶ A) (e : A ≅ U) (e' : A' ≅ U)
    (s : T ⟶ U) (v : F U U ⟶ U)
    (hv : ∀ t : U ⟶ U, map t (𝟙 U) ≫ v = v ≫ t) :
    map f (𝟙 T) ≫ (map e'.inv s ≫ v) =
      (map e.inv s ≫ v) ≫ e'.inv ≫ f ≫ e.hom := by
  simp only [Category.assoc]
  rw [← hv (e'.inv ≫ f ≫ e.hom)]
  simp only [← Category.assoc, hcomp, Category.id_comp, Category.comp_id]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma reassoc_two {B : Type*} [Category B] {X Y Z Y' W : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Y') (i : Y' ⟶ Z)
    (e : f ≫ g = h ≫ i) (k : Z ⟶ W) : f ≫ g ≫ k = h ≫ i ≫ k :=
  (Category.assoc f g k).symm.trans
    ((congrArg (fun z ↦ z ≫ k) e).trans (Category.assoc h i k))

private lemma triple_cancel {B : Type*} [Category B] {D H V U : B}
    (d : D ≅ U) (r : V ≅ U) (c : H ≅ V) :
    (d ≪≫ r.symm ≪≫ c.symm).hom ≫ c.hom ≫ r.hom = d.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private lemma triple_square {B : Type*} [Category B] {D₁ D₀ H₁ H₀ V₁ V₀ U : B}
    (d₁ : D₁ ≅ U) (d₀ : D₀ ≅ U) (r₁ : V₁ ≅ U) (r₀ : V₀ ≅ U)
    (c₁ : H₁ ≅ V₁) (c₀ : H₀ ≅ V₀) (δD : D₁ ⟶ D₀) (δH : H₁ ⟶ H₀) (g : U ⟶ U)
    (hH : δH ≫ c₀.hom ≫ r₀.hom = c₁.hom ≫ r₁.hom ≫ g)
    (hD : δD ≫ d₀.hom = d₁.hom ≫ g) :
    (d₁ ≪≫ r₁.symm ≪≫ c₁.symm).hom ≫ δH =
      δD ≫ (d₀ ≪≫ r₀.symm ≪≫ c₀.symm).hom := by
  apply (cancel_mono (c₀.hom ≫ r₀.hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hH]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hD.symm

private lemma unit_end_commute {B : Type*} [Category B] [MonoidalCategory B]
    (f g : 𝟙_ B ⟶ 𝟙_ B) : f ≫ g = g ≫ f := by
  have hl : (λ_ (𝟙_ B)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ B)).hom = g ≫ f := by
    rw [leftUnitor_inv_comp_tensorHom_assoc, unitors_equal, rightUnitor_naturality]
    rw [unitors_inv_equal, Iso.inv_hom_id_assoc]
  have hr : (λ_ (𝟙_ B)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ B)).hom = f ≫ g := by
    rw [unitors_inv_equal, rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_naturality]
    rw [← unitors_inv_equal, Iso.inv_hom_id_assoc]
  exact hr.symm.trans hl

private structure UnitCorrectionData {B : Type*} [Category B] {A U : B}
    (c v : A ≅ U) where
  iso : U ≅ U
  normalize : c.hom ≫ iso.hom = v.hom

private def unitCorrectionData {B : Type*} [Category B] {A U : B} (c v : A ≅ U) :
    UnitCorrectionData c v :=
  ⟨c.symm ≪≫ v, by simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]⟩

private lemma component_eq {B : Type*} [Category B] [HasZeroMorphisms B]
    {L M : CochainComplex B ℤ} {f g : L ⟶ M} (h : f = g)
    {A : B} (s : A ⟶ L.X 0) : s ≫ f.f 0 = s ≫ g.f 0 :=
  congrArg (fun z : L.X 0 ⟶ M.X 0 ↦ s ≫ z) (HomologicalComplex.congr_hom h 0)

private lemma reassoc_three {B : Type*} [Category B] {X Y Z U V : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ U) (d : X ⟶ U)
    (e : f ≫ g ≫ h = d) (k : U ⟶ V) : f ≫ g ≫ h ≫ k = d ≫ k := by
  rw [← Category.assoc g h k, ← Category.assoc f (g ≫ h) k, e]

private structure DualData {B : Type*} [Category B] [HasZeroMorphisms B]
    (D H : CochainComplex B ℤ) (U : B)
    (c₀ : H.X 0 ⟶ U) (c₁ : H.X (-1) ⟶ U)
    (d₀ : D.X 0 ⟶ U) (d₁ : D.X (-1) ⟶ U) where
  iso : D ≅ H
  eval_zero : iso.hom.f 0 ≫ c₀ = d₀
  eval_neg : iso.hom.f (-1) ≫ c₁ = d₁

private structure TwoTermData {B : Type*} [Category B] [HasZeroMorphisms B]
    (D H : CochainComplex B ℤ) (e₀ : D.X 0 ≅ H.X 0) (e₁ : D.X (-1) ≅ H.X (-1)) where
  iso : D ≅ H
  hom_zero : iso.hom.f 0 = e₀.hom
  hom_neg : iso.hom.f (-1) = e₁.hom

private def twoTermData {B : Type*} [Category B] [HasZeroMorphisms B]
    (D H : CochainComplex B ℤ) (e₀ : D.X 0 ≅ H.X 0) (e₁ : D.X (-1) ≅ H.X (-1))
    (hD : ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (D.X n))
    (hH : ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (H.X n))
    (hd : e₁.hom ≫ H.d (-1) 0 = D.d (-1) 0 ≫ e₀.hom) :
    TwoTermData D H e₀ e₁ := by
  let e (n : ℤ) : D.X n ≅ H.X n := by
    by_cases hn : n = 0
    · subst n
      exact e₀
    · by_cases hn' : n = -1
      · subst n
        exact e₁
      · exact (hD n hn' hn).iso (hH n hn' hn)
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_, ?_, ?_⟩
  · intro n k hnk
    have hk : k = n + 1 := hnk.symm
    subst k
    by_cases hn : n = -1
    · subst n
      simpa [e] using hd
    · by_cases hn0 : n = 0
      · subst n
        exact (hH 1 (by decide) (by decide)).eq_of_tgt _ _
      · exact (hD n hn hn0).eq_of_src _ _
  · simp [HomologicalComplex.Hom.isoOfComponents_hom_f, e]
  · simp [HomologicalComplex.Hom.isoOfComponents_hom_f, e]

private def assembleDual {B : Type*} [Category B] [HasZeroMorphisms B]
    (D H : CochainComplex B ℤ) {U V₀ V₁ : B}
    (d₀ : D.X 0 ≅ U) (d₁ : D.X (-1) ≅ U)
    (r₀ : V₀ ≅ U) (r₁ : V₁ ≅ U) (c₀ : H.X 0 ≅ V₀) (c₁ : H.X (-1) ≅ V₁)
    (hD : ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (D.X n))
    (hH : ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (H.X n))
    (g : U ⟶ U)
    (hHδ : H.d (-1) 0 ≫ c₀.hom ≫ r₀.hom = c₁.hom ≫ r₁.hom ≫ g)
    (hDδ : D.d (-1) 0 ≫ d₀.hom = d₁.hom ≫ g) :
    DualData D H U (c₀.hom ≫ r₀.hom) (c₁.hom ≫ r₁.hom) d₀.hom d₁.hom := by
  let e₀ := d₀ ≪≫ r₀.symm ≪≫ c₀.symm
  let e₁ := d₁ ≪≫ r₁.symm ≪≫ c₁.symm
  let t := twoTermData D H e₀ e₁ hD hH
    (triple_square d₁ d₀ r₁ r₀ c₁ c₀ _ _ g hHδ hDδ)
  refine ⟨t.iso, ?_, ?_⟩
  · rw [t.hom_zero]
    exact triple_cancel d₀ r₀ c₀
  · rw [t.hom_neg]
    exact triple_cancel d₁ r₁ c₁

section Generic

variable {E : Type*} [Category E] [MonoidalCategory E] [BraidedCategory E]
  [MonoidalClosed E]

@[irreducible] private def dualProduct (X Y : E) :
    (ihom X).obj (𝟙_ E) ⊗ (ihom Y).obj (𝟙_ E) ⟶
      (ihom (X ⊗ Y)).obj (𝟙_ E) :=
  curry (tensorμ X Y _ _ ≫
    ((ihom.ev X).app (𝟙_ E) ⊗ₘ (ihom.ev Y).app (𝟙_ E)) ≫ (λ_ (𝟙_ E)).hom)

omit [MonoidalClosed E] in
private lemma interchange_evaluation (X Y D H : E) (f : X ⊗ D ⟶ 𝟙_ E)
    (g : Y ⊗ H ⟶ 𝟙_ E) :
    tensorμ X Y D H ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ E)).hom =
      (β_ Y X).inv ▷ (D ⊗ H) ≫ (α_ Y X (D ⊗ H)).hom ≫
        Y ◁ (α_ X D H).inv ≫ Y ◁ f ▷ H ≫ Y ◁ (λ_ H).hom ≫ g := by
  have h : tensorμ X Y D H ≫ (α_ (X ⊗ D) Y H).inv ≫
      (β_ Y (X ⊗ D)).inv ▷ H ≫ (α_ Y (X ⊗ D) H).hom =
    (β_ Y X).inv ▷ (D ⊗ H) ≫ (α_ Y X (D ⊗ H)).hom ≫
      Y ◁ (α_ X D H).inv := by
    simp [tensorμ, BraidedCategory.braiding_tensor_right_inv]
  erw [← reassoc_of% h, ← associator_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← BraidedCategory.braiding_inv_naturality_left,
    comp_whiskerRight_assoc]
  erw [braiding_inv_tensorUnit_right]
  simp only [tensorHom_def, Category.assoc, leftUnitor_naturality]
  monoidal

private lemma dualProduct_eq (X Y : E) :
    dualProduct X Y = ihomUnitTensorToIhom X ((ihom Y).obj (𝟙_ E)) ≫
      ihomUncurry Y X (𝟙_ E) ≫ (pre (β_ Y X).inv).app (𝟙_ E) := by
  apply uncurry_injective
  erw [dualProduct, uncurry_curry,
    ← Category.assoc (ihomUnitTensorToIhom X _) (ihomUncurry Y X _) _,
    uncurry_pre_app, uncurry_natural_left,
    uncurry_ihomUncurry]
  erw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    whiskerLeft_ihomUnitTensorToIhom_ev]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact interchange_evaluation X Y _ _ ((ihom.ev X).app _) ((ihom.ev Y).app _)

private lemma dualProduct_isIso (X Y : E) (hX : IsDualizable X) :
    IsIso (dualProduct X Y) := by
  let _ := hX.some
  let _ : HasLeftDual X := BraidedCategory.hasLeftDualOfHasRightDual
  have := isIso_ihomUnitTensorToIhom (ᘁX) X ((ihom Y).obj (𝟙_ E))
  have : IsIso ((pre (β_ Y X).inv).app (𝟙_ E)) := by
    refine ⟨⟨(pre (β_ Y X).hom).app _, ?_, ?_⟩⟩
    · erw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id]
      rfl
    · erw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id]
      rfl
  erw [dualProduct_eq]
  change IsIso (ihomUnitTensorToIhom X ((ihom Y).obj (𝟙_ E)) ≫
    (ihomCurryIso Y X (𝟙_ E)).inv ≫ (pre (β_ Y X).inv).app (𝟙_ E))
  infer_instance

@[irreducible] private def dualComparison {X D : E}
    (q : D ≅ (ihom X).obj (𝟙_ E)) (hX : IsDualizable X) (Y : E) :
    D ⊗ (ihom Y).obj (𝟙_ E) ≅ (ihom (X ⊗ Y)).obj (𝟙_ E) := by
  letI : IsIso (dualProduct X Y) := dualProduct_isIso X Y hX
  exact whiskerRightIso q ((ihom Y).obj (𝟙_ E)) ≪≫ asIso (dualProduct X Y)

private lemma dualComparison_hom {X D : E}
    (q : D ≅ (ihom X).obj (𝟙_ E)) (hX : IsDualizable X) (Y : E) :
    (dualComparison q hX Y).hom =
      q.hom ▷ (ihom Y).obj (𝟙_ E) ≫ dualProduct X Y := by
  delta dualComparison
  rfl

private lemma dualProduct_natural {X X' Y Y' : E} (f : X' ⟶ X) (g : Y' ⟶ Y) :
    ((pre f).app (𝟙_ E) ⊗ₘ (pre g).app (𝟙_ E)) ≫ dualProduct X' Y' =
      dualProduct X Y ≫ (pre (f ⊗ₘ g)).app (𝟙_ E) := by
  apply uncurry_injective
  erw [uncurry_natural_left, uncurry_pre_app, dualProduct, dualProduct,
    uncurry_curry, uncurry_curry]
  erw [tensorμ_natural_right_assoc, tensorμ_natural_left_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, id_tensor_pre_app_comp_ev]

private lemma dualComparison_natural_left {X X' D D' : E}
    (q : D ≅ (ihom X).obj (𝟙_ E)) (q' : D' ≅ (ihom X').obj (𝟙_ E))
    (hX : IsDualizable X) (hX' : IsDualizable X') (Y : E)
    (f : X' ⟶ X) (t : D ⟶ D')
    (ht : t ≫ q'.hom = q.hom ≫ (pre f).app (𝟙_ E)) :
    t ▷ (ihom Y).obj (𝟙_ E) ≫ (dualComparison q' hX' Y).hom =
      (dualComparison q hX Y).hom ≫ (pre (f ▷ Y)).app (𝟙_ E) := by
  rw [dualComparison_hom, dualComparison_hom]
  rw [← comp_whiskerRight_assoc, ht, comp_whiskerRight_assoc]
  have h := dualProduct_natural f (𝟙 Y)
  simpa only [pre_id, NatTrans.id_app, tensorHom_id, Category.assoc] using
    congrArg (fun z ↦ q.hom ▷ (ihom Y).obj (𝟙_ E) ≫ z) h

private lemma dualComparison_natural_right {X D Y Y' : E}
    (q : D ≅ (ihom X).obj (𝟙_ E)) (hX : IsDualizable X) (f : Y' ⟶ Y) :
    D ◁ (pre f).app (𝟙_ E) ≫ (dualComparison q hX Y').hom =
      (dualComparison q hX Y).hom ≫ (pre (X ◁ f)).app (𝟙_ E) := by
  rw [dualComparison_hom, dualComparison_hom, whisker_exchange_assoc]
  have h := dualProduct_natural (𝟙 X) f
  simpa only [pre_id, NatTrans.id_app, id_tensorHom, Category.assoc] using
    congrArg (fun z ↦ q.hom ▷ (ihom Y).obj (𝟙_ E) ≫ z) h

private lemma dualProduct_unit {X Y : E} (f : X ⟶ 𝟙_ E) (g : Y ⟶ 𝟙_ E) :
    (λ_ (𝟙_ E)).inv ≫ (curry' f ⊗ₘ curry' g) ≫ dualProduct X Y =
      curry' ((f ⊗ₘ g) ≫ (λ_ (𝟙_ E)).hom) := by
  apply uncurry_injective
  conv_rhs => erw [curry', uncurry_curry]
  erw [uncurry_natural_left, uncurry_natural_left, dualProduct, uncurry_curry]
  erw [tensorμ_natural_right_assoc, tensorHom_comp_tensorHom_assoc,
    whiskerLeft_curry'_ihom_ev_app, whiskerLeft_curry'_ihom_ev_app]
  erw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  erw [← tensor_right_unitality_assoc]

omit [BraidedCategory E] in
private lemma curry_unit_pre {X : E} (p : X ⟶ 𝟙_ E) :
    curry' p = curry (λ_ (𝟙_ E)).hom ≫ (pre p).app (𝟙_ E) := by
  delta curry'
  have h : (ρ_ X).hom ≫ p = p ▷ (𝟙_ E) ≫ (λ_ (𝟙_ E)).hom := by
    rw [unitors_equal (C := E), rightUnitor_naturality]
  rw [h, ← curry_pre_app]

omit [BraidedCategory E] in
private lemma pre_eq_of_curry_source {P P' N : E} (f : P' ⟶ P)
    (s : (ihom P).obj N ⟶ (ihom P').obj N)
    (hs : ∀ {K : E} (g : P ⊗ K ⟶ N), curry (f ▷ K ≫ g) = curry g ≫ s) :
    (pre f).app N = s := by
  rw [← curry_uncurry ((pre f).app N), uncurry_pre, hs,
    ← uncurry_id_eq_ev, curry_uncurry, Category.id_comp]

private lemma dualComparison_unit {X D Y : E}
    (q : D ≅ (ihom X).obj (𝟙_ E)) (hX : IsDualizable X)
    (a : X ⟶ 𝟙_ E) (p : Y ⟶ 𝟙_ E) (j : 𝟙_ E ⟶ D)
    (hj : curry' a = j ≫ q.hom) :
    (λ_ (𝟙_ E)).inv ≫ (j ⊗ₘ curry' p) ≫ (dualComparison q hX Y).hom =
      curry' ((a ⊗ₘ p) ≫ (λ_ (𝟙_ E)).hom) := by
  rw [dualComparison_hom]
  have h := dualProduct_unit a p
  rw [hj, ← tensorHom_comp_whiskerRight] at h
  simpa only [Category.assoc] using h

private theorem dualComparisonFamily_exists {I : Type*} (P D : I → E)
    (q : ∀ i, D i ≅ (ihom (P i)).obj (𝟙_ E)) (hP : ∀ i, IsDualizable (P i)) :
    ∃ e : ∀ (i : I) (Y : E),
        D i ⊗ (ihom Y).obj (𝟙_ E) ≅ (ihom (P i ⊗ Y)).obj (𝟙_ E),
      (∀ (i : I) (Y : E), (e i Y).hom = (dualComparison (q i) (hP i) Y).hom) ∧
      (∀ (i : I) (Y Y' : E) (f : Y' ⟶ Y),
        D i ◁ (pre f).app (𝟙_ E) ≫ (e i Y').hom =
          (e i Y).hom ≫ (pre (P i ◁ f)).app (𝟙_ E)) ∧
      (∀ (i i' : I) (Y : E) (f : P i' ⟶ P i) (t : D i ⟶ D i'),
        t ≫ (q i').hom = (q i).hom ≫ (pre f).app (𝟙_ E) →
        t ▷ (ihom Y).obj (𝟙_ E) ≫ (e i' Y).hom =
          (e i Y).hom ≫ (pre (f ▷ Y)).app (𝟙_ E)) ∧
      (∀ (i : I) (Y : E) (a : P i ⟶ 𝟙_ E) (p : Y ⟶ 𝟙_ E)
          (j : 𝟙_ E ⟶ D i), curry' a = j ≫ (q i).hom →
        (λ_ (𝟙_ E)).inv ≫ (j ⊗ₘ curry' p) ≫ (e i Y).hom =
          curry' ((a ⊗ₘ p) ≫ (λ_ (𝟙_ E)).hom)) := by
  refine ⟨fun i Y ↦ dualComparison (q i) (hP i) Y, ?_, ?_, ?_, ?_⟩
  · intro i Y
    rfl
  · intro i Y Y' f
    exact dualComparison_natural_right (q i) (hP i) f
  · intro i i' Y f t ht
    exact dualComparison_natural_left (q i) (q i') (hP i) (hP i') Y f t ht
  · intro i Y a p j hj
    exact dualComparison_unit (q i) (hP i) a p j hj

end Generic

section HomFunctor

variable {E : Type*} [Category E] [MonoidalCategory E] [BraidedCategory E]

@[instance_reducible] private def closedFromHomFunctor (F : Eᵒᵖ ⥤ E ⥤ E)
    (adj : ∀ X : E, tensorLeft X ⊣ F.obj (op X)) : MonoidalClosed E where
  closed X := { rightAdj := F.obj (op X), adj := adj X }

private theorem homFunctorComparisonFamily_exists (F : Eᵒᵖ ⥤ E ⥤ E)
    (adj : ∀ X : E, tensorLeft X ⊣ F.obj (op X)) :
    letI := closedFromHomFunctor F adj
    ∀ (I : Type*) (P D : I → E)
      (q : ∀ i, D i ≅ (F.obj (op (P i))).obj (𝟙_ E))
      (_hP : ∀ i, IsDualizable (P i))
      (_hpre : ∀ {X X' : E} (f : X' ⟶ X) (N : E),
        (pre f).app N = (F.map f.op).app N),
    ∃ e : ∀ (i : I) (Y : E),
        ((curriedTensor E).obj (D i)).obj ((F.obj (op Y)).obj (𝟙_ E)) ≅
          (F.obj (op (((curriedTensor E).obj (P i)).obj Y))).obj (𝟙_ E),
      (∀ (i : I) (Y Y' : E) (f : Y' ⟶ Y),
        ((curriedTensor E).obj (D i)).map ((F.map f.op).app (𝟙_ E)) ≫ (e i Y').hom =
          (e i Y).hom ≫ (F.map (((curriedTensor E).obj (P i)).map f).op).app (𝟙_ E)) ∧
      (∀ (i i' : I) (Y : E) (f : P i' ⟶ P i) (t : D i ⟶ D i'),
        t ≫ (q i').hom = (q i).hom ≫ (F.map f.op).app (𝟙_ E) →
        ((curriedTensor E).map t).app _ ≫ (e i' Y).hom =
          (e i Y).hom ≫ (F.map (((curriedTensor E).map f).app Y).op).app (𝟙_ E)) ∧
      (∀ (i : I) (Y : E) (a : P i ⟶ 𝟙_ E) (p : Y ⟶ 𝟙_ E)
          (j : 𝟙_ E ⟶ D i), curry' a = j ≫ (q i).hom →
        (λ_ (𝟙_ E)).inv ≫ (j ⊗ₘ curry' p) ≫ (e i Y).hom =
          curry' ((a ⊗ₘ p) ≫ (λ_ (𝟙_ E)).hom)) := by
  let := closedFromHomFunctor F adj
  intro I P D q hP hpre
  obtain ⟨e, _, hright, hleft, hunit⟩ := dualComparisonFamily_exists P D q hP
  refine ⟨e, ?_, ?_, hunit⟩
  · intro i Y Y' f
    have hn := hright i Y Y' f
    have ha := congrArg (fun z : (F.obj (op Y)).obj (𝟙_ E) ⟶
        (F.obj (op Y')).obj (𝟙_ E) ↦ D i ◁ z ≫ (e i Y').hom) (hpre f (𝟙_ E))
    have hb := congrArg (fun z : (F.obj (op (P i ⊗ Y))).obj (𝟙_ E) ⟶
        (F.obj (op (P i ⊗ Y'))).obj (𝟙_ E) ↦ (e i Y).hom ≫ z)
      (hpre (P i ◁ f) (𝟙_ E))
    exact ha.symm.trans (hn.trans hb)
  · intro i i' Y f t ht
    have ht' : t ≫ (q i').hom = (q i).hom ≫ (pre f).app (𝟙_ E) :=
      ht.trans (congrArg (fun z ↦ (q i).hom ≫ z) (hpre f (𝟙_ E)).symm)
    have hn := hleft i i' Y f t ht'
    exact hn.trans (congrArg (fun z :
      (F.obj (op (P i ⊗ Y))).obj (𝟙_ E) ⟶
        (F.obj (op (P i' ⊗ Y))).obj (𝟙_ E) ↦ (e i Y).hom ≫ z)
      (hpre (f ▷ Y) (𝟙_ E)))

end HomFunctor

section GenericComplex

variable {B : Type w} [Category.{v} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive B] [MonoidalClosed B] [BraidedCategory B]
  [HasColimitsOfSize.{0, 0} B]

omit [MonoidalClosed B] [BraidedCategory B] in
private theorem genericComplexTensorExists (K L : CochainComplex B ℤ) :
    HomologicalComplex.HasTensor K L := inferInstance

attribute [local instance] genericComplexTensorExists

@[instance_reducible] private def genericComplexMonoidal :
    MonoidalCategory (CochainComplex B ℤ) := inferInstance

attribute [local instance] genericComplexMonoidal

@[instance_reducible] private def genericComplexMonoidalStruct :
    MonoidalCategoryStruct (CochainComplex B ℤ) :=
  genericComplexMonoidal.toMonoidalCategoryStruct

attribute [local instance] genericComplexMonoidalStruct

private lemma single_tensor_zero_generic {D H : CochainComplex B ℤ}
    (f : (𝟙_ (CochainComplex B ℤ)) ⟶ D) (g : (𝟙_ (CochainComplex B ℤ)) ⟶ H) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((𝟙_ B))).inv ≫
        (λ_ ((𝟙_ (CochainComplex B ℤ)))).inv.f 0 ≫ (f ⊗ₘ g).f 0 =
      (λ_ ((𝟙_ B))).inv ≫
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f.f 0 ⊗ₘ
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ g.f 0) ≫
        HomologicalComplex.ιTensorObj D H 0 0 0 (by omega) := by
  have hm : HomologicalComplex.ιTensorObj
      ((𝟙_ (CochainComplex B ℤ))) ((𝟙_ (CochainComplex B ℤ))) 0 0 0 (by omega) ≫
        (f ⊗ₘ g).f 0 =
      (f.f 0 ⊗ₘ g.f 0) ≫ HomologicalComplex.ιTensorObj D H 0 0 0 (by omega) := by
    change _ ≫ (HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)).f 0 = _
    erw [HomologicalComplex.ι_mapBifunctorMap]
    simpa only [curriedTensor_map_app, curriedTensor_obj_map] using
      (tensorHom_def_assoc (f.f 0) (g.f 0)
        (HomologicalComplex.ιTensorObj D H 0 0 0 (by omega))).symm
  erw [CochainComplex.leftUnitor_inv_f]
  simp only [Category.assoc]
  erw [hm, leftUnitor_inv_naturality_assoc,
    ← tensorHom_def'_assoc, tensorHom_comp_tensorHom_assoc]

end GenericComplex

attribute [local instance 20000] ringedCompletionHasSheafCompose

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

attribute [local irreducible] homComplexFunctor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

local instance ringedNegativeKoszulFactorHomTensorInst1 : MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).1.some

local instance ringedNegativeKoszulFactorHomTensorInst2
    : HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

@[instance_reducible] private def moduleMonoidal :
    MonoidalCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) := inferInstance

attribute [local instance] moduleMonoidal

@[instance_reducible] private def moduleMonoidalStruct :
    MonoidalCategoryStruct (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (moduleMonoidal O).toMonoidalCategoryStruct

attribute [local instance] moduleMonoidalStruct

private theorem complexTensorExists (K L : ringedSiteComplex O) :
    HomologicalComplex.HasTensor K L := inferInstance

attribute [local instance] complexTensorExists

@[instance_reducible] private def complexMonoidal :
    MonoidalCategory (ringedSiteComplex O) :=
  letI : MonoidalClosed (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    Classical.choice (SheafOfModules.tensorClosed O).2.1
  inferInstance

attribute [local instance] complexMonoidal

@[instance_reducible] private def complexMonoidalStruct :
    MonoidalCategoryStruct (ringedSiteComplex O) :=
  (complexMonoidal O).toMonoidalCategoryStruct

attribute [local instance] complexMonoidalStruct ringedComplexClosed

private abbrev RMod :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

private abbrev RUnit :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)

private abbrev RHom (L M : ringedSiteComplex O) : ringedSiteComplex O :=
  ((homComplexFunctor (R := O)).obj (op L)).obj M

private lemma ring_complex_unit :
    𝟙_ (ringedSiteComplex O) = ringedSiteRingComplex O := rfl

private lemma hom_zero_target {M N N' : RMod O} (f : M ⟶ M) :
    SheafOfModules.homObjMap (R := O) f (0 : N ⟶ N') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver O.obj X.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver O.obj X.unop).map (0 : N ⟶ N').val = 0
  ext W x
  rfl

private lemma dependent_iso {D : Type*} [Category D] {A : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (A ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi

private lemma single_projection_iso (L : ringedSiteComplex O) (n : ℤ) :
    IsIso (homComplexπ (R := O) L (ringedSiteRingComplex O) n (-n) 0 (by omega)) := by
  classical
  let M := ringedSiteRingComplex O
  let H := RHom O L M
  let Q := fun p : ℤ ↦ SheafOfModules.homObj (R := O) (L.X p) (M.X (p + n))
  let hc := homComplexIsLimit (R := O) L M n
  have hz (p : ℤ) (h : p ≠ -n) : IsZero (Q p) := by
    have ht : IsZero (M.X (p + n)) :=
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ _ (by omega)
    apply (IsZero.iff_id_eq_zero _).mpr
    change 𝟙 (SheafOfModules.homObj (R := O) (L.X p) (M.X (p + n))) = 0
    erw [← SheafOfModules.homObjMap_id (R := O), ht.eq_of_tgt (𝟙 _) 0]
    exact hom_zero_target O _
  let v : Q (-n) ⟶ H.X n := Fan.IsLimit.lift hc
    (fun p ↦ if h : p = -n then eqToHom (congrArg Q h.symm) else 0)
  have hv : v ≫ homComplexπ (R := O) L M n (-n) (-n + n) rfl = 𝟙 (Q (-n)) := by
    change Fan.IsLimit.lift hc _ ≫
      (Fan.mk (H.X n) (fun p : ℤ ↦ homComplexπ (R := O) L M n p (p + n) rfl)).proj (-n) = _
    erw [Fan.IsLimit.fac]
    simp
  have hπ : homComplexπ (R := O) L M n (-n) (-n + n) rfl ≫ v = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext hc
    intro p
    change (homComplexπ (R := O) L M n (-n) (-n + n) rfl ≫ v) ≫
      homComplexπ (R := O) L M n p (p + n) rfl = 𝟙 _ ≫ homComplexπ (R := O) L M n p (p + n) rfl
    by_cases h : p = -n
    · subst p
      erw [Category.assoc, hv, Category.comp_id]
    · exact (hz p h).eq_of_tgt _ _
  have hi : IsIso (homComplexπ (R := O) L M n (-n) (-n + n) rfl) :=
    (Iso.mk _ v hπ hv).isIso_hom
  exact dependent_iso (fun q h ↦ homComplexπ (R := O) L M n (-n) q h) (by omega) hi

private lemma unit_pre_eval (f : End (RUnit O)) :
    SheafOfModules.homObjMap (R := O) f.asHom (𝟙 _) ≫
        (SheafOfModules.homObjUnitIso.{u} (R := O) (RUnit O)).hom =
      (SheafOfModules.homObjUnitIso.{u} (R := O) (RUnit O)).hom ≫ f.asHom := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  let φX : O.obj.obj X →ₗ[O.obj.obj X] O.obj.obj X :=
    (φ.app (op (Over.mk (𝟙 X.unop)))).hom
  let fX : O.obj.obj X →ₗ[O.obj.obj X] O.obj.obj X := (f.asHom.val.app X).hom
  change φX (fX 1) = fX (φX 1)
  have h₁ := φX.map_smul (fX 1) 1
  have h₂ := fX.map_smul (φX 1) 1
  simpa only [smul_eq_mul, mul_one] using h₁.trans ((mul_comm _ _).trans h₂.symm)

attribute [local irreducible] SheafOfModules.homObj SheafOfModules.homObjMap
  SheafOfModules.homObjUnitIso

private abbrev TargetUnit := (ringedSiteRingComplex O).X 0

private abbrev StandardRankOneData {A : RMod O} (e : A ≅ RUnit O) :=
  IsoWithHom (SheafOfModules.homObjMap (R := O) e.inv
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).hom ≫
      (SheafOfModules.homObjUnitIso.{u} (R := O) (RUnit O)).hom)

@[irreducible] private def standardRankOneData {A : RMod O} (e : A ≅ RUnit O) :
    StandardRankOneData O e :=
  bifunctorMapIsoData (SheafOfModules.homObj (R := O))
    (fun f g ↦ SheafOfModules.homObjMap (R := O) f g)
    (fun _ _ ↦ SheafOfModules.homObjMap_id (R := O))
    (fun f f' g g' ↦ SheafOfModules.homObjMap_comp_homObjMap (R := O) f f' g g') e
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O))
    (SheafOfModules.homObjUnitIso.{u} (R := O) (RUnit O))

@[irreducible] private def standardRankOneDualIso {A : RMod O} (e : A ≅ RUnit O) :
    SheafOfModules.homObj (R := O) A (TargetUnit O) ≅ RUnit O :=
  (standardRankOneData O e).iso

private lemma standardRankOneDualIso_hom {A : RMod O} (e : A ≅ RUnit O) :
    (standardRankOneDualIso O e).hom = SheafOfModules.homObjMap (R := O) e.inv
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).hom ≫
        (SheafOfModules.homObjUnitIso.{u} (R := O) (RUnit O)).hom := by
  delta standardRankOneDualIso
  exact (standardRankOneData O e).hom_eq

private lemma standardRankOneDualIso_natural {A A' : RMod O} (f : A' ⟶ A)
    (e : A ≅ RUnit O) (e' : A' ≅ RUnit O) :
    SheafOfModules.homObjMap (R := O) f (𝟙 _) ≫ (standardRankOneDualIso O e').hom =
      (standardRankOneDualIso O e).hom ≫ e'.inv ≫ f ≫ e.hom := by
  erw [standardRankOneDualIso_hom, standardRankOneDualIso_hom]
  exact bifunctorMapEval_natural (SheafOfModules.homObj (R := O))
    (fun f g ↦ SheafOfModules.homObjMap (R := O) f g)
    (fun f f' g g' ↦ SheafOfModules.homObjMap_comp_homObjMap (R := O) f f' g g')
    f e e' _ _ (fun g ↦ unit_pre_eval O (End.of g))

@[irreducible] private def coordinateIso (L : ringedSiteComplex O) (n p : ℤ) (h : p + n = 0) :
    (RHom O L (ringedSiteRingComplex O)).X n ≅
      SheafOfModules.homObj (R := O) (L.X p) (TargetUnit O) := by
  let π := homComplexπ (R := O) L (ringedSiteRingComplex O) n p 0 h
  have hi : IsIso π := by
    obtain rfl : p = -n := by omega
    exact single_projection_iso O L n
  exact @asIso _ _ _ _ π hi

private lemma coordinateIso_hom (L : ringedSiteComplex O) (n p : ℤ) (h : p + n = 0) :
    (coordinateIso O L n p h).hom =
      homComplexπ (R := O) L (ringedSiteRingComplex O) n p 0 h := by
  delta coordinateIso
  rfl

private lemma coordinateIso_d (L : ringedSiteComplex O) :
    (RHom O L (ringedSiteRingComplex O)).d (-1) 0 ≫
        (coordinateIso O L 0 0 (by omega)).hom =
      (coordinateIso O L (-1) 1 (by omega)).hom ≫
        SheafOfModules.homObjMap (R := O) (L.d 0 1) (𝟙 (TargetUnit O)) := by
  let M := ringedSiteRingComplex O
  have hd := homComplex_d_π (R := O) L M (-1) 0 0 0 (-1) 1
    (by omega) (by omega) (by omega) (by omega)
  have hz : SheafOfModules.homObjMap (R := O) (𝟙 (L.X 0)) (M.d (-1) 0) = 0 := by
    change SheafOfModules.homObjMap (R := O) (𝟙 _) (0 : M.X (-1) ⟶ M.X 0) = 0
    exact hom_zero_target O _
  simp only [coordinateIso_hom]
  erw [hz, comp_zero, zero_sub] at hd
  erw [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg] at hd
  exact hd

private lemma coordinateIso_d_assoc (L : ringedSiteComplex O) {A : RMod O}
    (k : SheafOfModules.homObj (R := O) (L.X 0) (TargetUnit O) ⟶ A) :
    (RHom O L (ringedSiteRingComplex O)).d (-1) 0 ≫
        (coordinateIso O L 0 0 (by omega)).hom ≫ k =
      (coordinateIso O L (-1) 1 (by omega)).hom ≫
        SheafOfModules.homObjMap (R := O) (L.d 0 1) (𝟙 (TargetUnit O)) ≫ k :=
  reassoc_two _ _ _ _ (coordinateIso_d O L) k

attribute [local irreducible] ringedHomUnitEvaluationIso

@[irreducible] private def unitCorrection :
    UnitCorrectionData
      (coordinateIso O (ringedSiteRingComplex O) 0 0 (by omega) ≪≫
        standardRankOneDualIso O (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)))
      (HomologicalComplex.Hom.isoApp
          (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)) 0 ≪≫
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)) :=
  unitCorrectionData _ _

@[irreducible] private def rankOneDualIso {A : RMod O} (e : A ≅ RUnit O) :
    SheafOfModules.homObj (R := O) A (TargetUnit O) ≅ RUnit O :=
  standardRankOneDualIso O e ≪≫ (unitCorrection O).iso

private lemma rankOneDualIso_hom {A : RMod O} (e : A ≅ RUnit O) :
    (rankOneDualIso O e).hom =
      (standardRankOneDualIso O e).hom ≫ (unitCorrection O).iso.hom := by
  delta rankOneDualIso
  exact Iso.trans_hom _ _

private lemma rankOneDualIso_natural {A A' : RMod O} (f : A' ⟶ A)
    (e : A ≅ RUnit O) (e' : A' ≅ RUnit O) :
    SheafOfModules.homObjMap (R := O) f (𝟙 _) ≫ (rankOneDualIso O e').hom =
      (rankOneDualIso O e).hom ≫ e'.inv ≫ f ≫ e.hom := by
  erw [rankOneDualIso_hom, rankOneDualIso_hom,
    ← Category.assoc, standardRankOneDualIso_natural]
  simpa only [Category.assoc] using
    congrArg (fun z : RUnit O ⟶ RUnit O ↦ (standardRankOneDualIso O e).hom ≫ z)
      (unit_end_commute (e'.inv ≫ f ≫ e.hom) (unitCorrection O).iso.hom)

@[irreducible] private def positiveZero (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedKoszulFactor O b m).X 0 ≅ RUnit O :=
  HomologicalComplex.doubleXIso₀ _ _

@[irreducible] private def positiveOne (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedKoszulFactor O b m).X 1 ≅ RUnit O :=
  HomologicalComplex.doubleXIso₁ _ _ (by decide)

@[irreducible] private def negativeZero (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedNegativeKoszulFactor O b m).X 0 ≅ RUnit O :=
  HomologicalComplex.doubleXIso₁ _ _ (by decide)

@[irreducible] private def negativeNeg (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedNegativeKoszulFactor O b m).X (-1) ≅ RUnit O :=
  HomologicalComplex.doubleXIso₀ _ _

@[irreducible] private def factorDualData
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    DualData (ringedNegativeKoszulFactor O b m)
      (RHom O (ringedKoszulFactor O b m) (ringedSiteRingComplex O)) (RUnit O)
      ((coordinateIso O (ringedKoszulFactor O b m) 0 0 (by omega)).hom ≫
        (rankOneDualIso O (positiveZero O b m)).hom)
      ((coordinateIso O (ringedKoszulFactor O b m) (-1) 1 (by omega)).hom ≫
        (rankOneDualIso O (positiveOne O b m)).hom)
      (negativeZero O b m).hom (negativeNeg O b m).hom := by
  let P := ringedKoszulFactor O b m
  let D := ringedNegativeKoszulFactor O b m
  let H := RHom O P (ringedSiteRingComplex O)
  have hz (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ -1) : IsZero (H.X n) :=
    IsZero.of_iso
      (((SheafOfModules.homFunctor O).flip.obj (TargetUnit O)).map_isZero
        (show IsZero (P.X (-n)) from
          HomologicalComplex.isZero_double_X _ _ (-n) (by omega) (by omega)).op)
      (coordinateIso O P n (-n) (by omega))
  apply assembleDual D H (negativeZero O b m) (negativeNeg O b m)
    (rankOneDualIso O (positiveZero O b m)) (rankOneDualIso O (positiveOne O b m))
    (coordinateIso O P 0 0 (by omega)) (coordinateIso O P (-1) 1 (by omega))
    (fun n h₁ h₀ ↦ HomologicalComplex.isZero_double_X _ _ n h₁ h₀)
    (fun n h₁ h₀ ↦ hz n h₀ h₁)
    ((positiveZero O b m).inv ≫ P.d 0 1 ≫ (positiveOne O b m).hom)
  · erw [coordinateIso_d_assoc,
      rankOneDualIso_natural O (P.d 0 1) (positiveOne O b m) (positiveZero O b m)]
  · simp [P, D, ringedKoszulFactor, ringedNegativeKoszulFactor,
      positiveOne, positiveZero, negativeNeg, negativeZero,
      HomologicalComplex.double_d, Category.assoc]

private abbrev factorDualIso (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :=
  (factorDualData O b m).iso

private lemma hom_source_f {L L' M : ringedSiteComplex O} (f : L' ⟶ L)
    (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor (R := O)).map f.op).app M).f n ≫
        homComplexπ (R := O) L' M n p q h =
      homComplexπ (R := O) L M n p q h ≫ SheafOfModules.homObjMap (R := O) (f.f p) (𝟙 _) := by
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
    homComplexFunctor_map_f_π (R := O) f (𝟙 M) n p q h

private lemma coordinateIso_natural {L L' : ringedSiteComplex O} (f : L' ⟶ L)
    (n p : ℤ) (h : p + n = 0) :
    (((homComplexFunctor (R := O)).map f.op).app (ringedSiteRingComplex O)).f n ≫
        (coordinateIso O L' n p h).hom =
      (coordinateIso O L n p h).hom ≫
        SheafOfModules.homObjMap (R := O) (f.f p) (𝟙 (TargetUnit O)) := by
  erw [coordinateIso_hom, coordinateIso_hom]
  exact hom_source_f O f n p 0 h

private lemma coordinateIso_natural_assoc {L L' : ringedSiteComplex O}
    (f : L' ⟶ L) (n p : ℤ) (h : p + n = 0) {A : RMod O}
    (a : SheafOfModules.homObj (R := O) (L'.X p) (TargetUnit O) ⟶ A) :
    (((homComplexFunctor (R := O)).map f.op).app (ringedSiteRingComplex O)).f n ≫
        (coordinateIso O L' n p h).hom ≫ a =
      (coordinateIso O L n p h).hom ≫
        SheafOfModules.homObjMap (R := O) (f.f p) (𝟙 (TargetUnit O)) ≫ a := by
  erw [← Category.assoc, coordinateIso_natural, Category.assoc]

private lemma unit_dual_evaluation :
    (coordinateIso O (ringedSiteRingComplex O) 0 0 (by omega)).hom ≫
        (rankOneDualIso O (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _)).hom =
      (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom := by
  erw [rankOneDualIso_hom]
  exact (Category.assoc _ _ _).symm.trans (unitCorrection O).normalize

private lemma unit_dual_evaluation_assoc {A : RMod O} (k : RUnit O ⟶ A) :
    (coordinateIso O (ringedSiteRingComplex O) 0 0 (by omega)).hom ≫
        (rankOneDualIso O (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _)).hom ≫ k =
      (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).hom.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom ≫ k :=
  reassoc_two _ _ _ _ (unit_dual_evaluation O) k

private lemma factorDualIso_eval_zero
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (factorDualIso O b m).hom.f 0 ≫
        (coordinateIso O (ringedKoszulFactor O b m) 0 0 (by omega)).hom ≫
        (rankOneDualIso O (positiveZero O b m)).hom =
      (negativeZero O b m).hom := by
  delta factorDualIso
  exact (factorDualData O b m).eval_zero

private lemma factorDualIso_eval_neg
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (factorDualIso O b m).hom.f (-1) ≫
        (coordinateIso O (ringedKoszulFactor O b m) (-1) 1 (by omega)).hom ≫
        (rankOneDualIso O (positiveOne O b m)).hom =
      (negativeNeg O b m).hom := by
  delta factorDualIso
  exact (factorDualData O b m).eval_neg

private lemma factorDualIso_eval_zero_assoc
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) {A : RMod O}
    (k : RUnit O ⟶ A) :
    (factorDualIso O b m).hom.f 0 ≫
        (coordinateIso O (ringedKoszulFactor O b m) 0 0 (by omega)).hom ≫
        (rankOneDualIso O (positiveZero O b m)).hom ≫ k =
      (negativeZero O b m).hom ≫ k :=
  reassoc_three _ _ _ _ (factorDualIso_eval_zero O b m) k

private lemma factorDualIso_eval_neg_assoc
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) {A : RMod O}
    (k : RUnit O ⟶ A) :
    (factorDualIso O b m).hom.f (-1) ≫
        (coordinateIso O (ringedKoszulFactor O b m) (-1) 1 (by omega)).hom ≫
        (rankOneDualIso O (positiveOne O b m)).hom ≫ k =
      (negativeNeg O b m).hom ≫ k :=
  reassoc_three _ _ _ _ (factorDualIso_eval_neg O b m) k

attribute [local irreducible] ringedNegativeKoszulFactorTransition
  ringedNegativeKoszulFactorTransitionF ringedKoszulFactorStep ringedKoszulFactorStepF
  ringedKoszulFactorProjection ringedKoszulFactorProjectionF ringedNegativeKoszulFactorBasis

@[irreducible] private def factorInclusion (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedSiteRingComplex O ⟶ ringedNegativeKoszulFactor O b m :=
  HomologicalComplex.mkHomFromSingle (ringedNegativeKoszulFactorBasis O b m 0) (by
    intro k hk
    dsimp only [ringedNegativeKoszulFactor]
    erw [HomologicalComplex.double_d_eq_zero₀ _ _ 0 k (by decide), comp_zero]
    rfl)

private lemma negative_transition_neg
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedNegativeKoszulFactorTransition O b m).f (-1) ≫
        (negativeNeg O b m).hom =
      (negativeNeg O b (m + 1)).hom ≫ (ringedKoszulScalar O b).asHom := by
  delta ringedNegativeKoszulFactorTransition ringedNegativeKoszulFactorTransitionF
    negativeNeg ringedNegativeKoszulFactor
  simp only [Int.reduceNeg, ↓reduceDIte, Category.assoc]
  erw [eqToHom_refl, Category.id_comp]
  erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private lemma negative_transition_zero
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedNegativeKoszulFactorTransition O b m).f 0 ≫ (negativeZero O b m).hom =
      (negativeZero O b (m + 1)).hom := by
  delta ringedNegativeKoszulFactorTransition ringedNegativeKoszulFactorTransitionF
    negativeZero ringedNegativeKoszulFactor
  simp only [Int.reduceNeg, zero_eq_neg, one_ne_zero, ↓reduceDIte, Category.assoc]
  erw [eqToHom_refl, Category.id_comp]
  erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private lemma positive_step_one
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedKoszulFactorStep O b m).f 1 ≫ (positiveOne O b (m + 1)).hom =
      (positiveOne O b m).hom ≫ (ringedKoszulScalar O b).asHom := by
  delta ringedKoszulFactorStep ringedKoszulFactorStepF positiveOne ringedKoszulFactor
  simp only [one_ne_zero, ↓reduceDIte, Category.assoc]
  erw [eqToHom_refl, Category.id_comp]
  erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private lemma positive_step_zero
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedKoszulFactorStep O b m).f 0 ≫ (positiveZero O b (m + 1)).hom =
      (positiveZero O b m).hom := by
  delta ringedKoszulFactorStep ringedKoszulFactorStepF positiveZero ringedKoszulFactor
  simp only [↓reduceDIte, Category.assoc]
  erw [eqToHom_refl, Category.id_comp]
  erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private lemma factorDualIso_transition
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedNegativeKoszulFactorTransition O b m ≫ (factorDualIso O b m).hom =
      (factorDualIso O b (m + 1)).hom ≫
        ((homComplexFunctor (R := O)).map (ringedKoszulFactorStep O b m).op).app
          (ringedSiteRingComplex O) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = -1
  · subst n
    apply (cancel_mono ((coordinateIso O (ringedKoszulFactor O b m) (-1) 1 (by omega)).hom ≫
      (rankOneDualIso O (positiveOne O b m)).hom)).mp
    repeat' erw [HomologicalComplex.comp_f]
    repeat' erw [Category.assoc]
    erw [factorDualIso_eval_neg, coordinateIso_natural_assoc,
      rankOneDualIso_natural O _ (positiveOne O b (m + 1)) (positiveOne O b m)]
    simp only [factorDualIso_eval_neg_assoc]
    rw [negative_transition_neg, positive_step_one]
    simp only [Iso.inv_hom_id_assoc]
  · by_cases hn0 : n = 0
    · subst n
      apply (cancel_mono ((coordinateIso O (ringedKoszulFactor O b m) 0 0 (by omega)).hom ≫
        (rankOneDualIso O (positiveZero O b m)).hom)).mp
      repeat' erw [HomologicalComplex.comp_f]
      repeat' erw [Category.assoc]
      erw [factorDualIso_eval_zero, coordinateIso_natural_assoc,
        rankOneDualIso_natural O _ (positiveZero O b (m + 1)) (positiveZero O b m)]
      simp only [factorDualIso_eval_zero_assoc]
      rw [negative_transition_zero, positive_step_zero]
      simp only [Iso.inv_hom_id, Category.comp_id]
    · exact (show IsZero ((ringedNegativeKoszulFactor O b (m + 1)).X n) from
        HomologicalComplex.isZero_double_X _ _ n hn hn0).eq_of_src _ _

private lemma factorInclusion_f_zero
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (factorInclusion O b m).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).hom ≫
        ringedNegativeKoszulFactorBasis O b m 0 := by
  delta factorInclusion
  exact HomologicalComplex.mkHomFromSingle_f _ _

private lemma factorInclusion_zero
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (factorInclusion O b m).f 0 ≫ (negativeZero O b m).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).hom := by
  delta factorInclusion
  erw [HomologicalComplex.mkHomFromSingle_f]
  delta ringedNegativeKoszulFactorBasis negativeZero
  simp only [Int.reduceNeg, zero_eq_neg, one_ne_zero, ↓reduceDIte, Category.assoc]
  erw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id]
  rfl

private lemma factorProjection_zero
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    (ringedKoszulFactorProjection O b m).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).hom =
      (positiveZero O b m).hom := by
  delta ringedKoszulFactorProjection ringedKoszulFactorProjectionF positiveZero
  simp only [↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma factorDualIso_inclusion
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    factorInclusion O b m ≫ (factorDualIso O b m).hom =
      (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
        ((homComplexFunctor (R := O)).map
          (ringedKoszulFactorProjection O b m).op).app (ringedSiteRingComplex O) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    apply (cancel_mono ((coordinateIso O (ringedKoszulFactor O b m) 0 0 (by omega)).hom ≫
      (rankOneDualIso O (positiveZero O b m)).hom)).mp
    repeat' erw [HomologicalComplex.comp_f]
    repeat' erw [Category.assoc]
    erw [factorDualIso_eval_zero, coordinateIso_natural_assoc,
      rankOneDualIso_natural O _ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _)
        (positiveZero O b m)]
    simp only [unit_dual_evaluation_assoc]
    erw [factorInclusion_zero, factorProjection_zero]
    have hi := (HomologicalComplex.Hom.isoApp
      (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)) 0).inv_hom_id
    erw [← Category.assoc, hi]
    simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (RUnit O) n hn).eq_of_src _ _

attribute [local irreducible] ringedKoszulFactor ringedNegativeKoszulFactor ringedKoszulScalar

attribute [local irreducible] MonoidalClosed.curry MonoidalClosed.curry'
  MonoidalClosed.pre

private lemma hom_pre {P P' : ringedSiteComplex O} (f : P' ⟶ P)
    (N : ringedSiteComplex O) :
    (pre f).app N = ((homComplexFunctor (R := O)).map f.op).app N := by
  have hc {K : ringedSiteComplex O} (g : P ⊗ K ⟶ N) :
      curry (f ▷ K ≫ g) = curry g ≫
        ((homComplexFunctor (R := O)).map f.op).app N := by
    apply HomologicalComplex.hom_ext
    intro n
    apply homComplex_hom_ext
    intro p q h
    have hs := homComplexFunctor_map_f_π (R := O) f (𝟙 N) n p q h
    simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at hs
    erw [HomologicalComplex.comp_f, Category.assoc, hs, ← Category.assoc,
      ringedComplexCurry_component, ringedComplexCurry_component, Linear.units_smul_comp]
    congr 1
    erw [← SheafOfModules.pre_app (R := O) (f.f p) (N.X q), curry_pre_app]
    congr 1
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun z ↦ z ≫ g.f q)
        (CochainComplex.Monoidal.ι_whiskerRight (L := K) f p n q h)
  exact pre_eq_of_curry_source f _ (fun g ↦ hc g)

private lemma unit_curry {K : ringedSiteComplex O} (p : K ⟶ ringedSiteRingComplex O) :
    curry' p = (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
      ((homComplexFunctor (R := O)).map p.op).app (ringedSiteRingComplex O) := by
  let U := 𝟙_ (ringedSiteComplex O)
  let p' : K ⟶ U := p
  let v : U ⟶ (ihom U).obj U := (ringedHomUnitEvaluationIso O U).inv
  let s : (ihom U).obj U ⟶ (ihom K).obj U :=
    ((homComplexFunctor (R := O)).map p'.op).app U
  have hv : curry (λ_ U).hom = v :=
    (ringedComplexHomUnit_eq_curry O U).symm.trans (ringedComplexHomUnit_eq O U)
  have hs : (pre p').app U = s := hom_pre O p' U
  change curry' p' = v ≫ s
  exact (curry_unit_pre p').trans
    (congrArg₂ (fun (a : U ⟶ (ihom U).obj U)
      (c : (ihom U).obj U ⟶ (ihom K).obj U) ↦ a ≫ c) hv hs)

private lemma functional_zero {K : ringedSiteComplex O}
    (p : K ⟶ ringedSiteRingComplex O) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv ≫
        ((ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
          ((homComplexFunctor (R := O)).map p.op).app (ringedSiteRingComplex O)).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv ≫
        (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv.f 0 ≫
          (((homComplexFunctor (R := O)).map p.op).app (ringedSiteRingComplex O)).f 0 := by
  exact (congrArg
    (fun z ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv ≫ z)
    (HomologicalComplex.comp_f _ _ 0)).trans (Category.assoc _ _ _).symm

private lemma single_tensor_zero {D H : ringedSiteComplex O}
    (f : ringedSiteRingComplex O ⟶ D) (g : ringedSiteRingComplex O ⟶ H) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv ≫
        (λ_ (ringedSiteRingComplex O)).inv.f 0 ≫ (f ⊗ₘ g).f 0 =
      (λ_ (RUnit O)).inv ≫
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ f.f 0 ⊗ₘ
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ g.f 0) ≫
        HomologicalComplex.ιTensorObj D H 0 0 0 (by omega) :=
  single_tensor_zero_generic f g

private lemma koszul_functional {P K : ringedSiteComplex O}
    (a : P ⟶ ringedSiteRingComplex O) (p : K ⟶ ringedSiteRingComplex O) :
    (((ringedKoszulTensor O).map a).app K ≫
        ((ringedKoszulTensor O).obj (ringedSiteRingComplex O)).map p ≫
          (ringedKoszulUnitTensorIso O).hom) =
      (a ⊗ₘ p) ≫ (λ_ (ringedSiteRingComplex O)).hom := by
  change a ▷ K ≫ ringedSiteRingComplex O ◁ p ≫
    (λ_ (ringedSiteRingComplex O)).hom = _
  exact (tensorHom_def_assoc a p _).symm

private lemma factor_tensor_zero (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ)
    {H T : ringedSiteComplex O} (g : ringedSiteRingComplex O ⟶ H)
    (η : ringedNegativeKoszulFactor O b m ⊗ H ⟶ T) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv ≫
        ((λ_ (ringedSiteRingComplex O)).inv ≫
          (factorInclusion O b m ⊗ₘ g) ≫ η).f 0 =
      (λ_ (RUnit O)).inv ≫
        (ringedNegativeKoszulFactorBasis O b m 0 ⊗ₘ
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv ≫ g.f 0)) ≫
        HomologicalComplex.ιTensorObj (ringedNegativeKoszulFactor O b m) H 0 0 0
          (by omega) ≫ η.f 0 := by
  simp only [HomologicalComplex.comp_f]
  erw [reassoc_of% (single_tensor_zero O (factorInclusion O b m) g)]
  erw [factorInclusion_f_zero, Iso.inv_hom_id_assoc]

private lemma factor_normalization
    (b : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (K : ringedSiteComplex O)
    (p : K ⟶ ringedSiteRingComplex O)
    (η : ringedNegativeKoszulFactor O b m ⊗
      RHom O K (ringedSiteRingComplex O) ⟶
        RHom O (ringedKoszulFactor O b m ⊗ K) (ringedSiteRingComplex O))
    (hu : (λ_ (ringedSiteRingComplex O)).inv ≫
      (factorInclusion O b m ⊗ₘ
        ((ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
          ((homComplexFunctor (R := O)).map p.op).app (ringedSiteRingComplex O))) ≫ η =
      (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
        ((homComplexFunctor (R := O)).map
          (((ringedKoszulFactorProjection O b m ⊗ₘ p) ≫
            (λ_ (ringedSiteRingComplex O)).hom)).op).app (ringedSiteRingComplex O)) :
        (MonoidalCategory.leftUnitor
            (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
          MonoidalCategory.tensorHom (ringedNegativeKoszulFactorBasis O b m 0)
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
              (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv.f 0 ≫
              (((homComplexFunctor (R := O)).map p.op).app _).f 0) ≫
          CochainComplex.ιMapBifunctor (ringedNegativeKoszulFactor O b m)
            (RHom O K (ringedSiteRingComplex O))
            (MonoidalCategory.curriedTensor _) 0 0 0 (by omega) ≫ η.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv.f 0 ≫
          (((homComplexFunctor (R := O)).map
            (((ringedKoszulTensor O).map (ringedKoszulFactorProjection O b m)).app K ≫
              ((ringedKoszulTensor O).obj (ringedSiteRingComplex O)).map p ≫
              (ringedKoszulUnitTensorIso O).hom).op).app _).f 0 := by
  let a := ringedKoszulFactorProjection O b m
  let p' := p
  let U := ringedSiteRingComplex O
  let gp := (ringedHomUnitEvaluationIso O U).inv ≫
    ((homComplexFunctor (R := O)).map p.op).app U
  have hu₀ := component_eq (B := RMod O) hu
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv
  have hl := factor_tensor_zero O b m gp η
  have hr := functional_zero O ((a ⊗ₘ p') ≫ (λ_ U).hom)
  have ht := hl.symm.trans (hu₀.trans hr)
  dsimp only [gp] at ht
  erw [functional_zero O p] at ht
  erw [koszul_functional O]
  change (λ_ (RUnit O)).inv ≫
    (ringedNegativeKoszulFactorBasis O b m 0 ⊗ₘ
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (RUnit O)).inv ≫
        (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv.f 0 ≫
          (((homComplexFunctor (R := O)).map p.op).app
            (ringedSiteRingComplex O)).f 0)) ≫
      HomologicalComplex.ιTensorObj (ringedNegativeKoszulFactor O b m)
      (RHom O K (ringedSiteRingComplex O)) 0 0 0 (by omega) ≫ η.f 0 = _
  exact ht

attribute [-instance] moduleMonoidalStruct moduleMonoidal complexTensorExists

/-- Adjoining one positive factor inside Hom amounts to tensoring its negative factor.
This is a one-factor calculation with an arbitrary remaining complex `K`; it contains
no induction on a list of generators and no finite negative tensor.

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, the finite free dual identification, expanded for
one two-term factor and the tensor-Hom adjunction.
(auxiliary; not a blueprint node).

Proof: write `P = [O --b^(m+1)--> O]` in degrees 0,1 and
`D = [O --b^(m+1)--> O]` in degrees -1,0. Projection to the unique
nonzero target coordinate identifies each degree of Hom(P,O[0]) with the
corresponding internal Hom into O. Evaluation at one identifies its two
rank-one terms with those of D. Normalize them against the prescribed Hom-unit
isomorphism. The correction is an automorphism of O; unit endomorphisms commute,
so every scalar compatibility is preserved. The Hom differential in degree -1 is
positive precomposition, giving a chain isomorphism. It sends the inclusion
O[0] to D to the dual of the projection P to O[0], and intertwines the (b,1) and (1,b) steps.

In a braided closed category, tensoring two internal Homs into the unit and
then evaluating defines a natural product into Hom(P tensor K,O[0]).
The product factors through the closed currying isomorphism and the standard
map Hom(P,unit) tensor H to Hom(P,H). The latter is invertible because P
is dualizable. Applying this to the canonical dual identification gives e.
Naturality proves the first two equations. The product sends the tensor of
two curried functionals to the curry of their tensor followed by the unit
unitor. Taking degree zero and using the canonical tensor inclusion proves
the last equation, including its specified basis normalization.
The construction also applies to b=0, units b, zero ring sheaves, K=0,
and empty sites; it uses no inverses of sections or boundedness of K. -/
theorem ringedNegativeKoszulFactorHomTensor
    (b : (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : ∀ (m : ℕ) (K : ringedSiteComplex O),
      ((ringedKoszulTensor O).obj (ringedNegativeKoszulFactor O b m)).obj
          (homComplex (R := O) K (ringedSiteRingComplex O)) ≅
        homComplex (R := O)
          (((ringedKoszulTensor O).obj (ringedKoszulFactor O b m)).obj K)
          (ringedSiteRingComplex O),
      (∀ (m : ℕ) (K K' : ringedSiteComplex O) (f : K' ⟶ K),
        ((ringedKoszulTensor O).obj (ringedNegativeKoszulFactor O b m)).map
            (((homComplexFunctor (R := O)).map f.op).app _) ≫ (e m K').hom =
          (e m K).hom ≫ ((homComplexFunctor (R := O)).map
            (((ringedKoszulTensor O).obj (ringedKoszulFactor O b m)).map f).op).app _) ∧
      (∀ (m : ℕ) (K : ringedSiteComplex O),
        ((ringedKoszulTensor O).map
            (ringedNegativeKoszulFactorTransition O b m)).app _ ≫ (e m K).hom =
          (e (m + 1) K).hom ≫ ((homComplexFunctor (R := O)).map
            (((ringedKoszulTensor O).map (ringedKoszulFactorStep O b m)).app K).op).app _) ∧
      (∀ (m : ℕ) (K : ringedSiteComplex O) (p : K ⟶ ringedSiteRingComplex O),
        (MonoidalCategory.leftUnitor
            (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv ≫
          MonoidalCategory.tensorHom (ringedNegativeKoszulFactorBasis O b m 0)
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
              (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv.f 0 ≫
              (((homComplexFunctor (R := O)).map p.op).app _).f 0) ≫
          CochainComplex.ιMapBifunctor (ringedNegativeKoszulFactor O b m)
            (homComplex (R := O) K (ringedSiteRingComplex O))
            (MonoidalCategory.curriedTensor _) 0 0 0 (by omega) ≫ (e m K).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv.f 0 ≫
          (((homComplexFunctor (R := O)).map
            (((ringedKoszulTensor O).map (ringedKoszulFactorProjection O b m)).app K ≫
              ((ringedKoszulTensor O).obj (ringedSiteRingComplex O)).map p ≫
              (ringedKoszulUnitTensorIso O).hom).op).app _).f 0) := by
  let := moduleMonoidal O
  let := moduleMonoidalStruct O
  let : ∀ K L : ringedSiteComplex O, HomologicalComplex.HasTensor K L :=
    complexTensorExists O
  let P (m : ℕ) := ringedKoszulFactor O b m
  let D (m : ℕ) := ringedNegativeKoszulFactor O b m
  let H (K : ringedSiteComplex O) := RHom O K (ringedSiteRingComplex O)
  have hP (m : ℕ) : IsDualizable (P m) :=
    (ringedKoszulStage_dualizable O 1 (fun _ ↦ b) m).of_iso
      (ringedKoszulRightUnitIso O (P m))
  obtain ⟨e, hright, hleft, hunit⟩ := homFunctorComparisonFamily_exists
    (homComplexFunctor (R := O)) (ringedComplexHomAdjunction O)
    ℕ P D (factorDualIso O b) hP
    (fun f N ↦ hom_pre O f N)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro m K K' f
    exact hright m K K' f
  · intro m K
    exact hleft (m + 1) m K (ringedKoszulFactorStep O b m)
      (ringedNegativeKoszulFactorTransition O b m) (factorDualIso_transition O b m)
  · intro m K p
    let U := 𝟙_ (ringedSiteComplex O)
    let a : P m ⟶ U := ringedKoszulFactorProjection O b m
    let p' : K ⟶ U := p
    let j : U ⟶ D m := factorInclusion O b m
    let q : D m ⟶ (ihom (P m)).obj U := (factorDualIso O b m).hom
    have hc : curry' a = j ≫ q :=
      (unit_curry O a).trans (factorDualIso_inclusion O b m).symm
    have hu := hunit m K a p' j hc
    let gp : U ⟶ H K :=
      (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
        ((homComplexFunctor (R := O)).map p.op).app (ringedSiteRingComplex O)
    have hp : curry' p' = gp := unit_curry O p
    erw [hp] at hu
    change (λ_ U).inv ≫ (j ⊗ₘ gp) ≫ (e m K).hom = _ at hu
    have hu' := hu.trans (unit_curry O ((a ⊗ₘ p') ≫ (λ_ U).hom))
    have hu := hu'
    simp only [j, p', a, U, ring_complex_unit O] at hu
    exact factor_normalization O b m K p (e m K).hom hu

end CategoryTheory
