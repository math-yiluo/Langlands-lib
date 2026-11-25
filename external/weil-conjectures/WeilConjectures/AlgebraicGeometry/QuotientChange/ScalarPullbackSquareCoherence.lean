/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.ScalarPullbackSquareCoherence

/-! # Scalar pullback square coherence

## References

* Stacks Project, Tags 03EK, 0D6D, 07A6 and 0E47
* Stacks 07A7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapHomotopyCategory
  AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback

private theorem scalarSquare_eqToIso_symm
    {C : Type*} [Category* C] {T : Type*} (F : T → C)
    {x y : T} (w : x = y) :
    (eqToIso (congrArg F w)).symm = eqToIso (congrArg F w.symm) := by
  subst y
  rfl

private theorem invert_normalization
    {C : Type*} [Category C] {X Y Z W : C} (b : X ≅ Y)
    (A : Y ⟶ Z) (B : X ⟶ W) (s : W ≅ Z)
    (h : b.hom ≫ A = B ≫ s.hom) : b.inv ≫ B = A ≫ s.inv := by
  rw [← cancel_epi b.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def homotopy_iso_map
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) : F.mapHomotopyCategory (.up ℤ) ≅ G.mapHomotopyCategory (.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
      NatTrans.mapHomotopyCategory_id]

set_option backward.isDefEq.respectTransparency false in
private theorem inverse_homotopy_square
    {A B C E Z : Type*} [Category A] [Category B] [Category C]
    [Category E] [Category Z] [Preadditive A] [Preadditive B]
    [Preadditive C] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ C} {I : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (Q : HomotopyCategory E (.up ℤ) ⥤ Z)
    (P : HomotopyCategory A (.up ℤ)) {X Y : Z} (b : X ≅ Y)
    (a : Y ⟶ Q.obj ((G.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj P)))
    (c : X ⟶ Q.obj ((I.mapHomotopyCategory (.up ℤ)).obj
      ((H.mapHomotopyCategory (.up ℤ)).obj P)))
    (w : b.hom ≫ a ≫ Q.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P) =
      c ≫ Q.map ((Functor.mapHomotopyCategoryCompIso e.symm (.up ℤ)).hom.app P)) :
    b.inv ≫ c = a ≫ Q.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have he : (Functor.mapHomotopyCategoryCompIso e.symm (.up ℤ)).hom.app
      ((HomotopyCategory.quotient _ _).obj P) =
      (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app
        ((HomotopyCategory.quotient _ _).obj P) := rfl
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at w
  erw [Q.map_id, Category.comp_id] at w
  rw [he] at w
  have hi := invert_normalization b a c
    (Q.mapIso ((homotopy_iso_map e.symm).app
      ((HomotopyCategory.quotient _ _).obj P))) w
  simpa only [Functor.mapIso_inv, Iso.app_inv, homotopy_iso_map, Iso.symm_inv] using hi

private theorem homotopy_coherence
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    [Preadditive A₀] [Preadditive A₁] [Preadditive A₂]
    [Preadditive B₀] [Preadditive B₁] [Preadditive B₂]
    {S : A₀ ⥤ A₂} {Sk : A₀ ⥤ A₁} {Sh : A₁ ⥤ A₂}
    {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂}
    {T : B₀ ⥤ B₂} {Tk : B₀ ⥤ B₁} {Th : B₁ ⥤ B₂}
    [S.Additive] [Sk.Additive] [Sh.Additive]
    [E₀.Additive] [E₁.Additive] [E₂.Additive]
    [T.Additive] [Tk.Additive] [Th.Additive]
    {a : S ⟶ Sk ⋙ Sh} {ph : Sh ⋙ E₂ ⟶ E₁ ⋙ Th}
    {pk : Sk ⋙ E₁ ⟶ E₀ ⋙ Tk} {pc : S ⋙ E₂ ⟶ E₀ ⋙ T}
    {c : T ⟶ Tk ⋙ Th}
    (w : ∀ M, E₂.map (a.app M) ≫ ph.app (Sk.obj M) ≫ Th.map (pk.app M) =
      pc.app M ≫ c.app (E₀.obj M))
    (P : HomotopyCategory A₀ (.up ℤ)) :
    (E₂.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory a (.up ℤ)).app P) ≫
      (NatTrans.mapHomotopyCategory ph (.up ℤ)).app
        ((Sk.mapHomotopyCategory (.up ℤ)).obj P) ≫
      (Th.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory pk (.up ℤ)).app P) =
    (NatTrans.mapHomotopyCategory pc (.up ℤ)).app P ≫
      (NatTrans.mapHomotopyCategory c (.up ℤ)).app
        ((E₀.mapHomotopyCategory (.up ℤ)).obj P) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  ext n : 1
  simpa only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as, Functor.mapHomologicalComplex_obj_X] using w (P.X n)

private def homotopy_square_iso
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ C} {I : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) :
    F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ≅
      H.mapHomotopyCategory (.up ℤ) ⋙ I.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem homotopy_square_iso_hom_app
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ C} {I : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (P : HomotopyCategory A (.up ℤ)) :
    (homotopy_square_iso e).hom.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P) ≫
        (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem homotopy_compositor_hom_app
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    {F : A ⥤ C} {G : A ⥤ B} {H : B ⥤ C}
    [F.Additive] [G.Additive] [H.Additive]
    (e : F ≅ G ⋙ H) (P : HomotopyCategory A (.up ℤ)) :
    ((Functor.mapHomotopyCategoryCompIso e.symm (.up ℤ)).symm).hom.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rfl

private theorem homotopy_compositor_inv_app
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    {F : A ⥤ C} {G : A ⥤ B} {H : B ⥤ C}
    [F.Additive] [G.Additive] [H.Additive]
    (e : F ≅ G ⋙ H) (P : HomotopyCategory A (.up ℤ)) :
    ((Functor.mapHomotopyCategoryCompIso e.symm (.up ℤ)).symm).inv.app P =
      (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app P := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rfl

private theorem composite_counit_calculation
    {H₀ H₁ H₂ K₀ K₁ K₂ A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category H₀] [Category H₁] [Category H₂]
    [Category K₀] [Category K₁] [Category K₂]
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {Q₀ : H₀ ⥤ A₀} {Q₁ : H₁ ⥤ A₁} {Q₂ : H₂ ⥤ A₂}
    {R₀ : K₀ ⥤ B₀} {R₁ : K₁ ⥤ B₁} {R₂ : K₂ ⥤ B₂}
    {s₀ : H₀ ⥤ K₀} {s₁ : H₁ ⥤ K₁} {s₂ : H₂ ⥤ K₂}
    {d₀ : A₀ ⥤ B₀} {d₁ : A₁ ⥤ B₁} {d₂ : A₂ ⥤ B₂}
    {fk : A₀ ⥤ A₁} {fh : A₁ ⥤ A₂} {fc : A₀ ⥤ A₂}
    {gk : B₀ ⥤ B₁} {gh : B₁ ⥤ B₂} {gc : B₀ ⥤ B₂}
    {Fk : H₀ ⥤ H₁} {Fh : H₁ ⥤ H₂} {Fc : H₀ ⥤ H₂}
    {Gk : K₀ ⥤ K₁} {Gh : K₁ ⥤ K₂} {Gc : K₀ ⥤ K₂}
    (η₀ : Q₀ ⋙ d₀ ⟶ s₀ ⋙ R₀) (η₁ : Q₁ ⋙ d₁ ⟶ s₁ ⋙ R₁)
    (η₂ : Q₂ ⋙ d₂ ⟶ s₂ ⋙ R₂)
    (εk : Q₀ ⋙ fk ⟶ Fk ⋙ Q₁) (εh : Q₁ ⋙ fh ⟶ Fh ⋙ Q₂)
    (εc : Q₀ ⋙ fc ⟶ Fc ⋙ Q₂)
    (δk : R₀ ⋙ gk ⟶ Gk ⋙ R₁) (δh : R₁ ⋙ gh ⟶ Gh ⋙ R₂)
    (δc : R₀ ⋙ gc ⟶ Gc ⋙ R₂)
    (bk : fk ⋙ d₁ ⟶ d₀ ⋙ gk) (bh : fh ⋙ d₂ ⟶ d₁ ⋙ gh)
    (c : fc ≅ fk ⋙ fh) (c' : gc ≅ gk ⋙ gh)
    (a : Fc ≅ Fk ⋙ Fh) (a' : Gc ≅ Gk ⋙ Gh)
    (pk : Fk ⋙ s₁ ⟶ s₀ ⋙ Gk) (ph : Fh ⋙ s₂ ⟶ s₁ ⋙ Gh)
    (pc : Fc ⋙ s₂ ⟶ s₀ ⋙ Gc)
    (hk : ∀ P, bk.app (Q₀.obj P) ≫ gk.map (η₀.app P) ≫ δk.app (s₀.obj P) =
      d₁.map (εk.app P) ≫ η₁.app (Fk.obj P) ≫ R₁.map (pk.app P))
    (hh : ∀ P, bh.app (Q₁.obj P) ≫ gh.map (η₁.app P) ≫ δh.app (s₁.obj P) =
      d₂.map (εh.app P) ≫ η₂.app (Fh.obj P) ≫ R₂.map (ph.app P))
    (hc : ∀ P, c.hom.app (Q₀.obj P) ≫ fh.map (εk.app P) ≫ εh.app (Fk.obj P) =
      εc.app P ≫ Q₂.map (a.hom.app P))
    (hc' : ∀ P, c'.inv.app (R₀.obj P) ≫ δc.app P =
      gh.map (δk.app P) ≫ δh.app (Gk.obj P) ≫ R₂.map (a'.inv.app P))
    (w : ∀ P, s₂.map (a.hom.app P) ≫ ph.app (Fk.obj P) ≫ Gh.map (pk.app P) =
      pc.app P ≫ a'.hom.app (s₀.obj P))
    (P : H₀) :
    (d₂.map (c.hom.app (Q₀.obj P)) ≫ bh.app (fk.obj (Q₀.obj P)) ≫
      gh.map (bk.app (Q₀.obj P)) ≫ c'.inv.app (d₀.obj (Q₀.obj P))) ≫
      gc.map (η₀.app P) ≫ δc.app (s₀.obj P) =
    d₂.map (εc.app P) ≫ η₂.app (Fc.obj P) ≫ R₂.map (pc.app P) := by
  simp only [Category.assoc]
  have hn := c'.inv.naturality (η₀.app P)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, hc']
  rw [← gh.map_comp_assoc, ← gh.map_comp_assoc, Category.assoc, hk]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := δh.naturality (pk.app P)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hn := bh.naturality (εk.app P)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, reassoc_of% hh]
  rw [← d₂.map_comp_assoc, ← d₂.map_comp_assoc, Category.assoc, hc, d₂.map_comp]
  have hn := η₂.naturality (a.hom.app P)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  have hw := congrArg (fun q ↦ q ≫ a'.inv.app (s₀.obj P)) (w P)
  simp only [Category.assoc, Iso.hom_inv_id_app] at hw
  have hw' := hw.trans (Category.comp_id (obj := K₂) (pc.app P))
  simp only [← R₂.map_comp]
  rw [hw']

private theorem composition_hom_of_inv
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {d₀ : A₀ ⥤ B₀} {d₁ : A₁ ⥤ B₁} {d₂ : A₂ ⥤ B₂}
    {fk : A₀ ⥤ A₁} {fh : A₁ ⥤ A₂} {fc : A₀ ⥤ A₂}
    {gk : B₀ ⥤ B₁} {gh : B₁ ⥤ B₂} {gc : B₀ ⥤ B₂}
    (bk : d₀ ⋙ gk ≅ fk ⋙ d₁) (bh : d₁ ⋙ gh ≅ fh ⋙ d₂)
    (bc : d₀ ⋙ gc ≅ fc ⋙ d₂) (c : fc ≅ fk ⋙ fh) (c' : gc ≅ gk ⋙ gh)
    (w : ∀ M, bc.inv.app M = d₂.map (c.hom.app M) ≫
      bh.inv.app (fk.obj M) ≫ gh.map (bk.inv.app M) ≫ c'.inv.app (d₀.obj M))
    (M : A₀) :
    c'.hom.app (d₀.obj M) ≫ gh.map (bk.hom.app M) ≫ bh.hom.app (fk.obj M) =
      bc.hom.app M ≫ d₂.map (c.hom.app M) := by
  rw [← cancel_epi (bc.inv.app M)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [w]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← gh.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id (obj := B₂) _

private theorem paste_compositor_square
    {A B : Type*} [Category A] [Category B] (D : A ⥤ B)
    {X₀ X₁ X₂ X₃ : A} {Y₀ Y₁ Y₂ Y₃ : B}
    (c : X₀ ≅ X₁) (d : X₂ ≅ X₃) (t : X₀ ≅ X₂)
    (c' : Y₀ ≅ Y₁) (d' : Y₂ ≅ Y₃) (t' : Y₀ ≅ Y₂)
    (p : Y₁ ⟶ D.obj X₁) (q : Y₃ ⟶ D.obj X₃)
    (b : Y₀ ⟶ D.obj X₀) (b' : Y₂ ⟶ D.obj X₂)
    (hc : c'.hom ≫ p = b ≫ D.map c.hom)
    (hd : d'.hom ≫ q = b' ≫ D.map d.hom)
    (ht : t'.hom ≫ b' = b ≫ D.map t.hom) :
    p ≫ D.map (c.inv ≫ t.hom ≫ d.hom) =
      (c'.inv ≫ t'.hom ≫ d'.hom) ≫ q := by
  rw [← cancel_epi c'.hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hc, ← D.map_comp_assoc, Iso.hom_inv_id, D.map_id, Category.id_comp]
  rw [hd, reassoc_of% ht]

private theorem paste_evaluated_compositor_square
    {A A' B C : Type*} [Category A] [Category A'] [Category B] [Category C]
    (D : B ⥤ C) (S : A ⥤ A')
    {F₀ F₁ F₂ F₃ : A ⥤ B} {G₀ G₁ G₂ G₃ : A' ⥤ C}
    (c : F₀ ≅ F₁) (d : F₂ ≅ F₃) (t : F₀ ≅ F₂)
    (c' : G₀ ≅ G₁) (d' : G₂ ≅ G₃) (t' : G₀ ≅ G₂)
    (M : A) {Z Z' : C}
    (p₀ : G₁.obj (S.obj M) ⟶ Z) (p₁ : Z ⟶ D.obj (F₁.obj M))
    (q₀ : G₃.obj (S.obj M) ⟶ Z') (q₁ : Z' ⟶ D.obj (F₃.obj M))
    (b : G₀.obj (S.obj M) ⟶ D.obj (F₀.obj M))
    (b' : G₂.obj (S.obj M) ⟶ D.obj (F₂.obj M))
    (hc : c'.hom.app (S.obj M) ≫ p₀ ≫ p₁ = b ≫ D.map (c.hom.app M))
    (hd : d'.hom.app (S.obj M) ≫ q₀ ≫ q₁ = b' ≫ D.map (d.hom.app M))
    (ht : t'.hom.app (S.obj M) ≫ b' = b ≫ D.map (t.hom.app M)) :
    p₀ ≫ p₁ ≫ D.map ((c.symm ≪≫ t ≪≫ d).hom.app M) =
      (c'.symm ≪≫ t' ≪≫ d').hom.app (S.obj M) ≫ q₀ ≫ q₁ := by
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.app_hom,
    Iso.app_inv, Category.assoc] using
    paste_compositor_square D (c.app M) (d.app M) (t.app M)
      (c'.app (S.obj M)) (d'.app (S.obj M)) (t'.app (S.obj M)) (p₀ ≫ p₁)
      (q₀ ≫ q₁) b b' hc hd ht

private theorem paste_named_square
    {A A' B C : Type*} [Category A] [Category A'] [Category B] [Category C]
    (D : B ⥤ C) (S : A ⥤ A')
    {F₀ F₁ F₂ F₃ : A ⥤ B} {G₀ G₁ G₂ G₃ : A' ⥤ C}
    (c : F₀ ≅ F₁) (d : F₂ ≅ F₃) (t : F₀ ≅ F₂)
    (c' : G₀ ≅ G₁) (d' : G₂ ≅ G₃) (t' : G₀ ≅ G₂)
    (s : F₁ ≅ F₃) (s' : G₁ ≅ G₃)
    (hs : s = c.symm ≪≫ t ≪≫ d) (hs' : s' = c'.symm ≪≫ t' ≪≫ d')
    (M : A) {Z Z' : C}
    (p₀ : G₁.obj (S.obj M) ⟶ Z) (p₁ : Z ⟶ D.obj (F₁.obj M))
    (q₀ : G₃.obj (S.obj M) ⟶ Z') (q₁ : Z' ⟶ D.obj (F₃.obj M))
    (b : G₀.obj (S.obj M) ⟶ D.obj (F₀.obj M))
    (b' : G₂.obj (S.obj M) ⟶ D.obj (F₂.obj M))
    (hc : c'.hom.app (S.obj M) ≫ p₀ ≫ p₁ = b ≫ D.map (c.hom.app M))
    (hd : d'.hom.app (S.obj M) ≫ q₀ ≫ q₁ = b' ≫ D.map (d.hom.app M))
    (ht : t'.hom.app (S.obj M) ≫ b' = b ≫ D.map (t.hom.app M)) :
    p₀ ≫ p₁ ≫ D.map (s.hom.app M) = s'.hom.app (S.obj M) ≫ q₀ ≫ q₁ := by
  subst s s'
  exact paste_evaluated_compositor_square D S c d t c' d' t' M
    p₀ p₁ q₀ q₁ b b' hc hd ht

private theorem natTrans_app_eq_of_iso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (α β : F ⟶ G) {X Y : A} (e : X ≅ Y) (h : α.app X = β.app X) :
    α.app Y = β.app Y := by
  rw [← cancel_epi (F.map e.hom), α.naturality, β.naturality, h]

private theorem conjugate_scalar_comp
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂}
    {V₀ : B₀ ⥤ A₀} {V₁ : B₁ ⥤ A₁} {V₂ : B₂ ⥤ A₂}
    {Fk : A₀ ⥤ A₁} {Fh : A₁ ⥤ A₂} {Fc : A₀ ⥤ A₂}
    {Rk : A₁ ⥤ A₀} {Rh : A₂ ⥤ A₁} {Rc : A₂ ⥤ A₀}
    {Gk : B₀ ⥤ B₁} {Gh : B₁ ⥤ B₂} {Gc : B₀ ⥤ B₂}
    {Sk : B₁ ⥤ B₀} {Sh : B₂ ⥤ B₁} {Sc : B₂ ⥤ B₀}
    (e₀ : E₀ ⊣ V₀) (e₁ : E₁ ⊣ V₁) (e₂ : E₂ ⊣ V₂)
    (ak : Fk ⊣ Rk) (ah : Fh ⊣ Rh) (ac : Fc ⊣ Rc)
    (bk : Gk ⊣ Sk) (bh : Gh ⊣ Sh) (bc : Gc ⊣ Sc)
    (cA : Fc ≅ Fk ⋙ Fh) (cB : Gc ≅ Gk ⋙ Gh)
    (ph : Fh ⋙ E₂ ≅ E₁ ⋙ Gh) (pk : Fk ⋙ E₁ ≅ E₀ ⋙ Gk)
    (pc : Fc ⋙ E₂ ≅ E₀ ⋙ Gc)
    (w : (Functor.associator Sh Sk V₀) ≪≫
        Functor.isoWhiskerLeft Sh (conjugateIsoEquiv (e₀.comp bk) (ak.comp e₁) pk) ≪≫
        (Functor.associator Sh V₁ Rk).symm ≪≫
        Functor.isoWhiskerRight (conjugateIsoEquiv (e₁.comp bh) (ah.comp e₂) ph) Rk ≪≫
        Functor.associator V₂ Rh Rk ≪≫
        Functor.isoWhiskerLeft V₂ (conjugateIsoEquiv (ak.comp ah) ac cA) =
      Functor.isoWhiskerRight (conjugateIsoEquiv (bk.comp bh) bc cB) V₀ ≪≫
        conjugateIsoEquiv (e₀.comp bc) (ac.comp e₂) pc) :
    Functor.isoWhiskerRight cA E₂ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Fk ph ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight pk Gh ≪≫ Functor.associator _ _ _ =
    pc ≪≫ Functor.isoWhiskerLeft E₀ cB := by
  apply (conjugateIsoEquiv (e₀.comp (bk.comp bh)) (ac.comp e₂)).injective
  rw [conjugateIsoEquiv_trans _ ((ak.comp ah).comp e₂) _,
    conjugateIsoEquiv_trans _ (ak.comp (ah.comp e₂)) _,
    conjugateIsoEquiv_trans _ (ak.comp (e₁.comp bh)) _,
    conjugateIsoEquiv_trans _ ((ak.comp e₁).comp bh) _,
    conjugateIsoEquiv_trans _ ((e₀.comp bk).comp bh) _,
    conjugateIsoEquiv_trans _ (e₀.comp bc) _]
  simpa only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_isoWhiskerLeft,
    conjugateIsoEquiv_associator, conjugateIsoEquiv_iso_symm, Iso.trans_assoc] using w

namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private instance module_tensor_two
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B : GradedObject ℤ (Modules R T)) : A.HasTensor B := by
  intro j
  infer_instance

private instance module_tensor_four
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C E : GradedObject ℤ (Modules R T)) :
    GradedObject.HasTensor₄ObjExt A B C E := by
  intro i j
  infer_instance

private instance module_tensor_left
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  intro i j
  infer_instance

private instance module_tensor_right
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (A B C : GradedObject ℤ (Modules R T)) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  intro i j
  infer_instance

private theorem module_exists_kflat_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u})
    (M : DerivedCategory (Modules R T)) :
    ∃ P : HomotopyCategory (Modules R T) (.up ℤ),
      (HomotopyCategory.quasiIso (Modules R T) (.up ℤ)).kFlat P ∧
        Nonempty (DerivedCategory.Qh.obj P ≅ M) := by
  exact DerivedCategory.exists_kFlat_iso M

private instance module_kflat_derivable
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u}) :
    CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure
      (HomotopyCategory.quasiIso (Modules R T) (.up ℤ)).localizerMorphismKFlat := by
  infer_instance

private instance extension_kflat (φ : Λ ⟶ Λ') [IsMonHom φ] (T : Scheme.{u}) :
    (extension φ T).PreservesKFlatQuasiIso := by
  exact Mod.preservesKFlatQuasiIso (coefficientMap φ T)

private theorem scalar_counit_iso (φ : Λ ⟶ Λ') [IsMonHom φ]
    (T : Scheme.{u}) (P : HomotopyCategory (Modules Λ T) (.up ℤ))
    (hP : (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ)).kFlat P) :
    IsIso ((scalarCounit φ T).app P) := by
  unfold scalarCounit D
  change IsIso ((extension φ T).leftDerivedFunctorCounit.app P)
  exact (extension φ T).derives_kFlat.isIso_of_isLeftDerivedFunctor
    (extension φ T).leftDerivedFunctorCounit ⟨P, hP⟩

private theorem pull_counit_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U V : Scheme.{u}} (h : U ⟶ V)
    (P : HomotopyCategory (Modules R V) (.up ℤ)) :
    IsIso ((pullCounit (Λ := R) h).app P) := by
  change IsIso ((CondensedRing.upperStar R h).leftDerivedFunctorCounit.app P)
  have : IsIso (CondensedRing.upperStar R h).leftDerivedFunctorCounit :=
    Functor.isIso_leftDerivedFunctorCounit _
  exact NatIso.isIso_app_of_isIso _ P

/-- The typed square is the paste of the two canonical compositors. -/
theorem scalarPullbackSquare_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    ((eqToIso (congrArg (fun t : X' ⟶ Y ↦ L R t) sq.toCommSq.w)) ≪≫
      scalarPullbackComposition R f' c).symm ≪≫ scalarPullbackComposition R a f =
        scalarPullbackSquare R sq := by
  unfold scalarPullbackSquare
  simp only [Iso.trans_symm, Iso.trans_assoc]
  have hh := scalarSquare_eqToIso_symm
    (fun t : X' ⟶ Y ↦ L R t) sq.toCommSq.w
  exact congrArg (fun e ↦ (scalarPullbackComposition R f' c).symm ≪≫ e ≪≫
    scalarPullbackComposition R a f) hh

-- Specializing the categorical lemma searches instances on categories of module objects.
private theorem ordinary_scalar_comp (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    Functor.isoWhiskerRight (CondensedRing.upperStarComp Λ h k) (extension φ U) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (CondensedRing.upperStar Λ k) (CondensedRing.pullIso φ h) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.pullIso φ k) (CondensedRing.upperStar Λ' h) ≪≫
      Functor.associator _ _ _ =
    CondensedRing.pullIso φ (h ≫ k) ≪≫
      Functor.isoWhiskerLeft (extension φ W) (CondensedRing.upperStarComp Λ' h k) := by
  let eU := Mod.extendRestrictAdjunction (coefficientMap φ U)
  let eV := Mod.extendRestrictAdjunction (coefficientMap φ V)
  let eW := Mod.extendRestrictAdjunction (coefficientMap φ W)
  let ah := CondensedRing.upperStarLowerStarAdjunction Λ h
  let ak := CondensedRing.upperStarLowerStarAdjunction Λ k
  let ahk := CondensedRing.upperStarLowerStarAdjunction Λ (h ≫ k)
  let bh := CondensedRing.upperStarLowerStarAdjunction Λ' h
  let bk := CondensedRing.upperStarLowerStarAdjunction Λ' k
  let bhk := CondensedRing.upperStarLowerStarAdjunction Λ' (h ≫ k)
  apply conjugate_scalar_comp eW eV eU ak ah ahk bk bh bhk
  have hp (T₁ T₂ : Scheme.{u}) (t : T₁ ⟶ T₂) :
      conjugateIsoEquiv
        ((Mod.extendRestrictAdjunction (coefficientMap φ T₂)).comp
          (CondensedRing.upperStarLowerStarAdjunction Λ' t))
        ((CondensedRing.upperStarLowerStarAdjunction Λ t).comp
          (Mod.extendRestrictAdjunction (coefficientMap φ T₁)))
        (CondensedRing.pullIso φ t) = CondensedRing.comapLowerStarIso φ t := by
    unfold CondensedRing.pullIso Adjunction.pullIsoOfComapIso
    exact Equiv.apply_symm_apply _ _
  simp only [eU, eV, eW, ah, ak, ahk, bh, bk, bhk, hp,
    CondensedRing.conjugateIsoEquiv_upperStarComp]
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Mod.comp_hom', Mod.id_hom', CondensedRing.lowerStarComp_hom_app_hom,
    CondensedRing.lowerStar_map_hom]
  simp only [CondensedRing.comapLowerStarIso,
    Mod.comapMapModComapIso_hom_app_hom,
    Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStar Mod.extendScalars
  CondensedRing.upperStarComp CondensedRing.pullIso
  scalarCounit pullCounit

set_option backward.isDefEq.respectTransparency true in
-- The explicit homotopy functor interfaces require additional instance synthesis.
private theorem normalized_inv_fac (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U) (hb : PullNormalized φ h b)
    (P : HomotopyCategory (Modules Λ V) (.up ℤ)) :
    b.inv.app (DerivedCategory.Qh.obj P) ≫
        (L Λ' h).map ((scalarCounit φ V).app P) ≫
        (pullCounit (Λ := Λ') h).app
          (((extension φ V).mapHomotopyCategory (.up ℤ)).obj P) =
      (D φ U).map ((pullCounit (Λ := Λ) h).app P) ≫
        (scalarCounit φ U).app
          (((CondensedRing.upperStar Λ h).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (CondensedRing.pullIso φ h).hom (.up ℤ)).app P) := by
  have hi := inverse_homotopy_square
    (F := CondensedRing.upperStar Λ h) (G := extension φ U)
    (H := extension φ V) (I := CondensedRing.upperStar Λ' h)
    (CondensedRing.pullIso φ h) DerivedCategory.Qh P
    (b.app (DerivedCategory.Qh.obj P))
    ((D φ U).map ((pullCounit (Λ := Λ) h).app P) ≫
      (scalarCounit φ U).app
        (((CondensedRing.upperStar Λ h).mapHomotopyCategory (.up ℤ)).obj P))
    ((L Λ' h).map ((scalarCounit φ V).app P) ≫
      (pullCounit (Λ := Λ') h).app
        (((extension φ V).mapHomotopyCategory (.up ℤ)).obj P))
    (by simpa only [Iso.app_hom,
      Category.assoc (obj := DerivedCategory (Modules Λ' U))] using hb P)
  set_option backward.isDefEq.respectTransparency false in
    simpa only [Functor.comp_obj, Iso.app_inv,
      Category.assoc (obj := DerivedCategory (Modules Λ' U))] using hi

private def compositeInverse (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (bh : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (bk : D φ W ⋙ L Λ' k ≅ L Λ k ⋙ D φ V) :
    L Λ (h ≫ k) ⋙ D φ U ≅ D φ W ⋙ L Λ' (h ≫ k) :=
  Functor.isoWhiskerRight (scalarPullbackComposition Λ h k) (D φ U) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (L Λ k) bh.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight bk.symm (L Λ' h) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (D φ W) (scalarPullbackComposition Λ' h k).symm

set_option backward.isDefEq.respectTransparency false in
-- Specializing the categorical lemma searches instances on categories of module objects.
private theorem pull_comp_fac
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (P : HomotopyCategory (Modules R W) (.up ℤ)) :
    (scalarPullbackComposition R h k).hom.app (DerivedCategory.Qh.obj P) ≫
        (L R h).map ((pullCounit (Λ := R) k).app P) ≫
        (pullCounit (Λ := R) h).app
          (((CondensedRing.upperStar R k).mapHomotopyCategory (.up ℤ)).obj P) =
      (pullCounit (Λ := R) (h ≫ k)).app P ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (CondensedRing.upperStarComp R h k).hom (.up ℤ)).app P) := by
  unfold scalarPullbackComposition L CondensedRing.moduleObjectDerivedPullback pullCounit
  rw [CondensedRing.leftDerivedUpperStarComp_eq_leftDerivedFunctorFactorIso]
  exact Functor.leftDerivedFunctorFactorIso_hom_app_comp_counit
    (CondensedRing.upperStarComp R h k) P

private theorem pull_comp_inv_fac
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (P : HomotopyCategory (Modules R W) (.up ℤ)) :
    (scalarPullbackComposition R h k).inv.app (DerivedCategory.Qh.obj P) ≫
        (pullCounit (Λ := R) (h ≫ k)).app P =
      (L R h).map ((pullCounit (Λ := R) k).app P) ≫
        (pullCounit (Λ := R) h).app
          (((CondensedRing.upperStar R k).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (CondensedRing.upperStarComp R h k).inv (.up ℤ)).app P) := by
  have hi := invert_normalization ((scalarPullbackComposition R h k).app
      (DerivedCategory.Qh.obj P))
    ((L R h).map ((pullCounit (Λ := R) k).app P) ≫
      (pullCounit (Λ := R) h).app
        (((CondensedRing.upperStar R k).mapHomotopyCategory (.up ℤ)).obj P))
    ((pullCounit (Λ := R) (h ≫ k)).app P)
    (DerivedCategory.Qh.mapIso ((homotopy_iso_map
      (CondensedRing.upperStarComp R h k)).app P))
    (pull_comp_fac R h k P)
  simpa only [Functor.comp_obj,
    (Category.assoc (obj := DerivedCategory (Modules R U))), Functor.mapIso_inv, Iso.app_inv,
    homotopy_iso_map, Iso.symm_inv] using hi

set_option backward.isDefEq.respectTransparency false in
-- Specializing the categorical lemma searches instances on categories of module objects.
private theorem ordinary_scalar_comp_homotopy (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (P : HomotopyCategory (Modules Λ W) (.up ℤ)) :
    ((extension φ U).mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (CondensedRing.upperStarComp Λ h k).hom
          (.up ℤ)).app P) ≫
      (NatTrans.mapHomotopyCategory (CondensedRing.pullIso φ h).hom (.up ℤ)).app
        (((CondensedRing.upperStar Λ k).mapHomotopyCategory (.up ℤ)).obj P) ≫
      ((CondensedRing.upperStar Λ' h).mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (CondensedRing.pullIso φ k).hom (.up ℤ)).app P) =
    (NatTrans.mapHomotopyCategory (CondensedRing.pullIso φ (h ≫ k)).hom (.up ℤ)).app P ≫
      (NatTrans.mapHomotopyCategory (CondensedRing.upperStarComp Λ' h k).hom
        (.up ℤ)).app (((extension φ W).mapHomotopyCategory (.up ℤ)).obj P) := by
  apply homotopy_coherence
    (S := CondensedRing.upperStar Λ (h ≫ k))
    (Sk := CondensedRing.upperStar Λ k) (Sh := CondensedRing.upperStar Λ h)
    (E₀ := extension φ W) (E₁ := extension φ V) (E₂ := extension φ U)
    (T := CondensedRing.upperStar Λ' (h ≫ k))
    (Tk := CondensedRing.upperStar Λ' k) (Th := CondensedRing.upperStar Λ' h)
    (a := (CondensedRing.upperStarComp Λ h k).hom)
    (ph := (CondensedRing.pullIso φ h).hom)
    (pk := (CondensedRing.pullIso φ k).hom)
    (pc := (CondensedRing.pullIso φ (h ≫ k)).hom)
    (c := (CondensedRing.upperStarComp Λ' h k).hom)
  intro M
  have hh := congrArg (fun e ↦ e.hom.app M) (ordinary_scalar_comp φ h k)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Functor.comp_obj, Category.id_comp, Category.comp_id] using hh

set_option backward.isDefEq.respectTransparency false in
-- Bound elaboration while specializing the computation-counit calculation.
private theorem scalar_comp_inv (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (normalized : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized φ h (b h)) :
    (b (h ≫ k)).inv = (compositeInverse φ h k (b h) (b k)).hom := by
  apply NatTrans.ext
  funext M
  obtain ⟨P, hP, ⟨e⟩⟩ := module_exists_kflat_iso Λ W M
  apply natTrans_app_eq_of_iso
    (F := L Λ (h ≫ k) ⋙ D φ U) (G := D φ W ⋙ L Λ' (h ≫ k)) _ _ e
  have hs : IsIso ((scalarCounit φ W).app P) := scalar_counit_iso φ W P hP
  have hg := pull_counit_iso Λ' (h ≫ k)
    (((extension φ W).mapHomotopyCategory (.up ℤ)).obj P)
  let t := (L Λ' (h ≫ k)).map ((scalarCounit φ W).app P) ≫
    (pullCounit (Λ := Λ') (h ≫ k)).app
      (((extension φ W).mapHomotopyCategory (.up ℤ)).obj P)
  have : IsIso t := IsIso.comp_isIso' (Functor.map_isIso _ _) hg
  rw [← cancel_mono t]
  dsimp only [t]
  refine (normalized_inv_fac φ (h ≫ k) (b (h ≫ k))
    (normalized (h ≫ k)) P).trans ?_
  symm
  simp only [compositeInverse, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  have H := composite_counit_calculation
    (Q₀ := DerivedCategory.Qh (C := Modules Λ W))
    (Q₁ := DerivedCategory.Qh (C := Modules Λ V))
    (Q₂ := DerivedCategory.Qh (C := Modules Λ U))
    (R₀ := DerivedCategory.Qh (C := Modules Λ' W))
    (R₁ := DerivedCategory.Qh (C := Modules Λ' V))
    (R₂ := DerivedCategory.Qh (C := Modules Λ' U))
    (s₀ := (extension φ W).mapHomotopyCategory (.up ℤ))
    (s₁ := (extension φ V).mapHomotopyCategory (.up ℤ))
    (s₂ := (extension φ U).mapHomotopyCategory (.up ℤ))
    (d₀ := D φ W) (d₁ := D φ V) (d₂ := D φ U)
    (fk := L Λ k) (fh := L Λ h) (fc := L Λ (h ≫ k))
    (gk := L Λ' k) (gh := L Λ' h) (gc := L Λ' (h ≫ k))
    (Fk := (CondensedRing.upperStar Λ k).mapHomotopyCategory (.up ℤ))
    (Fh := (CondensedRing.upperStar Λ h).mapHomotopyCategory (.up ℤ))
    (Fc := (CondensedRing.upperStar Λ (h ≫ k)).mapHomotopyCategory (.up ℤ))
    (Gk := (CondensedRing.upperStar Λ' k).mapHomotopyCategory (.up ℤ))
    (Gh := (CondensedRing.upperStar Λ' h).mapHomotopyCategory (.up ℤ))
    (Gc := (CondensedRing.upperStar Λ' (h ≫ k)).mapHomotopyCategory (.up ℤ))
    (scalarCounit φ W) (scalarCounit φ V) (scalarCounit φ U)
    (pullCounit k) (pullCounit h) (pullCounit (h ≫ k))
    (pullCounit (Λ := Λ') k) (pullCounit (Λ := Λ') h)
    (pullCounit (Λ := Λ') (h ≫ k)) (b k).inv (b h).inv
    (scalarPullbackComposition Λ h k) (scalarPullbackComposition Λ' h k)
    (Functor.mapHomotopyCategoryCompIso (CondensedRing.upperStarComp Λ h k).symm
      (.up ℤ)).symm
    (Functor.mapHomotopyCategoryCompIso (CondensedRing.upperStarComp Λ' h k).symm
      (.up ℤ)).symm
    (homotopy_square_iso
      (F := CondensedRing.upperStar Λ k) (G := extension φ V)
      (H := extension φ W) (I := CondensedRing.upperStar Λ' k)
      (CondensedRing.pullIso φ k)).hom
    (homotopy_square_iso
      (F := CondensedRing.upperStar Λ h) (G := extension φ U)
      (H := extension φ V) (I := CondensedRing.upperStar Λ' h)
      (CondensedRing.pullIso φ h)).hom
    (homotopy_square_iso
      (F := CondensedRing.upperStar Λ (h ≫ k)) (G := extension φ U)
      (H := extension φ W) (I := CondensedRing.upperStar Λ' (h ≫ k))
      (CondensedRing.pullIso φ (h ≫ k))).hom
    (by
      intro Q
      simpa only [homotopy_square_iso_hom_app] using
        normalized_inv_fac φ k (b k) (normalized k) Q)
    (by
      intro Q
      simpa only [homotopy_square_iso_hom_app] using
        normalized_inv_fac φ h (b h) (normalized h) Q)
    ?_ ?_ ?_ P
  · simpa only [homotopy_square_iso_hom_app] using H
  · intro Q
    simpa only [homotopy_compositor_hom_app] using pull_comp_fac Λ h k Q
  · intro Q
    simpa only [homotopy_compositor_inv_app] using pull_comp_inv_fac Λ' h k Q
  · intro Q
    simpa only [homotopy_compositor_hom_app, homotopy_square_iso_hom_app] using
      ordinary_scalar_comp_homotopy φ h k Q

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_comp_hom (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (normalized : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized φ h (b h))
    (M : DerivedCategory (Modules Λ W)) :
    (scalarPullbackComposition Λ' h k).hom.app ((D φ W).obj M) ≫
        (L Λ' h).map ((b k).hom.app M) ≫ (b h).hom.app ((L Λ k).obj M) =
      (b (h ≫ k)).hom.app M ≫
        (D φ U).map ((scalarPullbackComposition Λ h k).hom.app M) := by
  apply composition_hom_of_inv (b k) (b h) (b (h ≫ k))
    (scalarPullbackComposition Λ h k) (scalarPullbackComposition Λ' h k)
  intro N
  rw [scalar_comp_inv φ h k b normalized]
  simp only [compositeInverse, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_congr (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} {h k : U ⟶ V} (w : h = k)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (M : DerivedCategory (Modules Λ V)) :
    (eqToIso (congrArg (fun t ↦ L Λ' t) w)).hom.app ((D φ V).obj M) ≫
        (b k).hom.app M =
      (b h).hom.app M ≫
        (D φ U).map ((eqToIso (congrArg (fun t ↦ L Λ t) w)).hom.app M) := by
  subst k
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact (Category.comp_id (obj := DerivedCategory (Modules Λ' U)) _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The scalar/pullback comparisons intertwine the canonical geometric square
compositors before taking any geometric mates. -/
theorem scalar_pullback_square_coherence (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (normalized : ∀ {U V : Scheme.{u}} (h : U ⟶ V), PullNormalized φ h (b h))
    (M : DerivedCategory (Modules Λ Y)) :
    (L Λ' f').map ((b c).hom.app M) ≫
        (b f').hom.app ((L Λ c).obj M) ≫
        (D φ X').map ((scalarPullbackSquare Λ sq).hom.app M) =
      (scalarPullbackSquare Λ' sq).hom.app ((D φ Y).obj M) ≫
        (L Λ' a).map ((b f).hom.app M) ≫ (b a).hom.app ((L Λ f).obj M) := by
  exact paste_named_square
    (A := DerivedCategory (Modules Λ Y)) (A' := DerivedCategory (Modules Λ' Y))
    (B := DerivedCategory (Modules Λ X')) (C := DerivedCategory (Modules Λ' X'))
    (D φ X') (D φ Y)
    (F₀ := L Λ (f' ≫ c)) (F₁ := L Λ c ⋙ L Λ f')
    (F₂ := L Λ (a ≫ f)) (F₃ := L Λ f ⋙ L Λ a)
    (G₀ := L Λ' (f' ≫ c)) (G₁ := L Λ' c ⋙ L Λ' f')
    (G₂ := L Λ' (a ≫ f)) (G₃ := L Λ' f ⋙ L Λ' a)
    (scalarPullbackComposition Λ f' c) (scalarPullbackComposition Λ a f)
    (eqToIso (congrArg (fun t : X' ⟶ Y ↦ L Λ t) sq.toCommSq.w.symm))
    (scalarPullbackComposition Λ' f' c) (scalarPullbackComposition Λ' a f)
    (eqToIso (congrArg (fun t : X' ⟶ Y ↦ L Λ' t) sq.toCommSq.w.symm))
    (scalarPullbackSquare Λ sq) (scalarPullbackSquare Λ' sq)
    (by unfold scalarPullbackSquare; rfl) (by unfold scalarPullbackSquare; rfl) M
    ((L Λ' f').map ((b c).hom.app M)) ((b f').hom.app ((L Λ c).obj M))
    ((L Λ' a).map ((b f).hom.app M)) ((b a).hom.app ((L Λ f).obj M))
    ((b (f' ≫ c)).hom.app M) ((b (a ≫ f)).hom.app M)
    (scalar_comp_hom φ f' c b normalized M)
    (scalar_comp_hom φ a f b normalized M)
    (scalar_congr φ sq.toCommSq.w.symm b M)

end AlgebraicGeometry.ProEtale.QuotientChange
