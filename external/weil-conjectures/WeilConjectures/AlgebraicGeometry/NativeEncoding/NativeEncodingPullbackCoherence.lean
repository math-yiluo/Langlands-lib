/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Coherence of the normalized ordinary native encoding

## References

* Stacks 03D7 and 0B65
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.NativeEncoding

private theorem push_hom (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : AdicSheaf l X) :
    ((pushComparison l f).hom.app M).hom = 𝟙 _ := by
  ext V m
  exact (Classical.choose_spec (encoding_ordinary_operations l f)).1 M V m

private theorem ordinary_mate (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (adicUpperStarLowerStarAdjunction l f)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (TwoSquare.mk _ _ _ _ (pullComparison l f).inv)) =
        (pushComparison l f).hom := by
  dsimp only [pullComparison, pushComparison]
  exact (Classical.choose_spec
    (Classical.choose_spec (encoding_ordinary_operations l f)).2).1

private theorem push_composition (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : AdicSheaf l X) :
    (pushComparison l g).hom.app ((adicLowerStar l f).obj M) ≫
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).map
        ((pushComparison l f).hom.app M) ≫
      (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g).hom.app
        ((encoding l X).obj M) =
    (encoding l Z).map ((adicLowerStarComp l f g).hom.app M) ≫
      (pushComparison l (f ≫ g)).hom.app M := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', push_hom, CondensedRing.lowerStar_map_hom,
    Category.id_comp, CondensedRing.lowerStarComp_hom_app_hom]
  ext V m
  rfl

attribute [local irreducible] adicUpperStar adicLowerStar
  CondensedRing.upperStar CondensedRing.lowerStar encoding pushComparison pullComparison

private theorem pull_composition (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : AdicSheaf l Z) :
    (encoding l X).map ((adicUpperStarComp l f g).inv.app M) ≫
      (pullComparison l (f ≫ g)).hom.app M =
    (pullComparison l f).hom.app ((adicUpperStar l g).obj M) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map
        ((pullComparison l g).hom.app M) ≫
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).inv.app
        ((encoding l Z).obj M) := by
  exact equivalenceAdjunctionComparison_compositor
    (equivalence l Z) (equivalence l Y) (equivalence l X)
    (adicUpperStarLowerStarAdjunction l g) (adicUpperStarLowerStarAdjunction l f)
    (adicUpperStarLowerStarAdjunction l (f ≫ g))
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (f ≫ g))
    (pushComparison l g) (pushComparison l f) (pushComparison l (f ≫ g))
    (pullComparison l g) (pullComparison l f) (pullComparison l (f ≫ g))
    (ordinary_mate l g) (ordinary_mate l f) (ordinary_mate l (f ≫ g))
    (adicLowerStarComp l f g)
    (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g)
    (push_composition l f g) (adicUpperStarComp l f g).symm
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).symm
    (conjugateEquiv_adicUpperStarComp_inv l f g)
    (by
      exact congrArg Iso.hom
        ((conjugateIsoEquiv _ _).apply_symm_apply
          (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) f g).symm)) M

private theorem invert_compositor
    {C : Type*} [Category C] {A B C' D : C}
    (a : A ≅ B) (b : C' ≅ D) (x : A ⟶ C') (y : B ⟶ D)
    (h : a.hom ≫ y = x ≫ b.hom) : a.inv ≫ x = y ≫ b.inv := by
  apply (cancel_epi a.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem invert_square
    {C : Type*} [Category C] {A B C' D E F : C}
    (a : A ≅ B) (b : B ≅ C') (c : D ≅ E) (d : E ≅ F)
    (x : A ⟶ D) (y : C' ⟶ F)
    (h : a.hom ≫ b.hom ≫ y = x ≫ c.hom ≫ d.hom) :
    b.inv ≫ a.inv ≫ x = y ≫ d.inv ≫ c.inv := by
  have he := invert_compositor (a ≪≫ b) (c ≪≫ d) x y
    (by simpa only [Iso.trans_hom, Category.assoc] using h)
  simpa only [Iso.trans_inv, Category.assoc] using he

private theorem native_congr (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    adicUpperStarCongr l h = eqToIso (congrArg (adicUpperStar l) h) := by
  cases h
  rfl

private theorem comparison_eq (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : AdicSheaf l Y) :
    (encoding l X).map ((eqToIso (congrArg (adicUpperStar l) h)).hom.app M) ≫
      (pullComparison l g).hom.app M =
    (pullComparison l f).hom.app M ≫
      (eqToIso (congrArg (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)) h)).hom.app
        ((encoding l Y).obj M) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  erw [(encoding l X).map_id, Category.id_comp]

private theorem inverse_comparison
    {C : Type*} [Category C] {A B D E F : C}
    (a : A ≅ B) (b : A ⟶ D) (c : B ⟶ E) (d : E ⟶ F) (e : D ≅ F)
    (h : a.inv ≫ b = c ≫ d ≫ e.inv) : a.hom ≫ c ≫ d = b ≫ e.hom := by
  apply (cancel_epi a.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [h]
  simp [Category.assoc]

private theorem paste_three
    {C : Type*} [Category C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (d : E ⟶ F) (e : F ⟶ D)
    (x : B ⟶ G) (y : D ⟶ H) (z : G ⟶ H)
    {I J K : C} (k : G ⟶ I) (l : I ⟶ J) (m : J ⟶ K) (n : H ⟶ K)
    (h₁ : a ≫ b = c ≫ d ≫ e) (he : x ≫ z = b ≫ y)
    (h₂ : k ≫ l ≫ m = z ≫ n) :
    c ≫ d ≫ e ≫ y ≫ n = a ≫ x ≫ k ≫ l ≫ m := by
  rw [← reassoc_of% h₁, ← reassoc_of% he, ← h₂]

private theorem ordinary_forward_cube (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : AdicSheaf l Y) :
    (pullComparison l p').hom.app ((adicUpperStar l g).obj M) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p').map
        ((pullComparison l g).hom.app M) ≫
      ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) p' g).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)) sq.w.symm) ≪≫
        CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) v p).hom.app
          ((encoding l Y).obj M) =
    (encoding l X').map (((adicUpperStarComp l p' g).symm ≪≫
        eqToIso (congrArg (adicUpperStar l) sq.w.symm) ≪≫ adicUpperStarComp l v p).hom.app M) ≫
      (pullComparison l v).hom.app ((adicUpperStar l p).obj M) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) v).map
        ((pullComparison l p).hom.app M) := by
  have hr := inverse_comparison
    ((encoding l X').mapIso ((adicUpperStarComp l v p).app M)) _ _ _
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) v p).app
      ((encoding l Y).obj M)) (pull_composition l v p M)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  exact paste_three _ _ _ _ _ _ _ _ _ _ _ _
    (pull_composition l p' g M) (comparison_eq l sq.w.symm M) hr

/-- The specified ordinary condensed pullback-square compositor, kept as a single
isomorphism so localization can use its components without expanding adjunction data. -/
@[irreducible] def condensedPullbackSquare (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g) :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p' ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) v :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) p' g).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)) sq.w.symm) ≪≫
      CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) v p

/-- The ordinary inverse-image comparisons commute with the specified square compositors. -/
theorem encoding_pullback_cube (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : AdicSheaf l Y) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p').map
        ((pullComparison l g).inv.app M) ≫
      (pullComparison l p').inv.app ((adicUpperStar l g).obj M) ≫
      (encoding l X').map ((adicUpperStarCompIso l sq.w.symm).hom.app M) =
    (condensedPullbackSquare l sq).hom.app
        ((encoding l Y).obj M) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) v).map
        ((pullComparison l p).inv.app M) ≫
      (pullComparison l v).inv.app ((adicUpperStar l p).obj M) := by
  rw [show condensedPullbackSquare l sq =
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) p' g).symm ≪≫
      eqToIso (congrArg (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
        sq.w.symm) ≪≫ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) v p from by
      delta condensedPullbackSquare
      rfl]
  rw [adicUpperStarCompIso, native_congr]
  exact invert_square
    ((pullComparison l p').app ((adicUpperStar l g).obj M))
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p').mapIso
      ((pullComparison l g).app M))
    ((pullComparison l v).app ((adicUpperStar l p).obj M))
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) v).mapIso
      ((pullComparison l p).app M)) _ _ (ordinary_forward_cube l sq M)

end AlgebraicGeometry.ProEtale.NativeEncoding
