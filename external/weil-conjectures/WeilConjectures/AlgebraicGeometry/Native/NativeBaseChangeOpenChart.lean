/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedBaseChange
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedForgetMate
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition

/-! # Open-chart compatibility of the native derived exchange

## References

* Stacks 09A5, pullback pasting
* Stacks 0D6G and 09T5
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  adicUpperStar adicLowerStar adicUpperStarComp adicLowerStarComp
  adicUpperStarCongr adicLowerStarCongr adicUpperStarLowerStarAdjunction

private theorem transport_symm {C : Type*} [Category C] {a b : C} (e : a = b) :
    eqToIso e.symm = (eqToIso e).symm := by
  cases e
  rfl

private theorem transport_hom_symm {C : Type*} [Category C] {a b : C} (e : a = b) :
    (eqToIso e.symm).hom = (eqToIso e).inv := by
  cases e
  rfl

private theorem heart_open_mate (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} [IsOpenImmersion v] [IsOpenImmersion g]
    (sq : CommSq v p' p g) :
    (mateEquiv (adicUpperStarLowerStarAdjunction l p)
      (adicUpperStarLowerStarAdjunction l p')
      (TwoSquare.mk _ _ _ _ (adicUpperStarCompIso l sq.w.symm).hom)) =
        adicBaseChangeMap l sq.flip := by
  apply (mateEquiv (adicUpperStarLowerStarAdjunction l v)
    (adicUpperStarLowerStarAdjunction l g)).injective
  rw [adicBaseChangeMap, Equiv.apply_symm_apply]
  change (mateEquiv (adicUpperStarLowerStarAdjunction l v)
    (adicUpperStarLowerStarAdjunction l g)
    (mateEquiv (adicUpperStarLowerStarAdjunction l p)
      (adicUpperStarLowerStarAdjunction l p')
      (TwoSquare.mk _ _ _ _ (adicUpperStarCompIso l sq.w.symm).hom))) =
        (adicSquareLowerStarIso l sq.flip).hom
  rw [iterated_mateEquiv_conjugateEquiv]
  change conjugateEquiv
    ((adicUpperStarLowerStarAdjunction l p).comp (adicUpperStarLowerStarAdjunction l v))
    ((adicUpperStarLowerStarAdjunction l g).comp (adicUpperStarLowerStarAdjunction l p'))
    ((adicUpperStarComp l p' g).inv ≫ (adicUpperStarCongr l sq.w.symm).hom ≫
      (adicUpperStarComp l v p).hom) = _
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (v ≫ p)),
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (p' ≫ g)),
    conjugateEquiv_adicUpperStarComp_hom, conjugateEquiv_adicUpperStarComp_inv]
  have hc : (adicUpperStarCongr l sq.w.symm).hom =
      (adicUpperStarCongr l sq.w).inv := by
    unfold adicUpperStarCongr
    exact transport_hom_symm
      (congrArg (fun f : X' ⟶ Y => adicUpperStar l f) sq.w)
  rw [hc, conjugateEquiv_adicUpperStarCongr_inv]
  rfl

private theorem derived_open_mate (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} [IsOpenImmersion v] [IsOpenImmersion g]
    (sq : IsPullback v p' p g) :
    adicDerivedBaseChange l sq.toCommSq = (adicDerivedBaseChangeIso l sq.flip).hom := by
  have := isIso_adicBaseChangeMap_of_isPullback l sq.flip
  have hs : (Functor.mapDerivedCategoryNatIso
      (adicUpperStarCompIso l sq.w.symm).symm).inv =
      (Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l sq.w.symm)).hom := by
    have he : Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l sq.w.symm).symm =
        (Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l sq.w.symm)).symm :=
      Iso.ext (Functor.mapDerivedCategoryNatIso_symm (adicUpperStarCompIso l sq.w.symm))
    exact congrArg Iso.inv he
  simpa only [adicDerivedBaseChange, adicDerivedPullSquare, adicDerivedBaseChangeIso, hs,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.trans_hom, Category.assoc] using
    Adjunction.derived_exact_forget_mate
    (adicUpperStarLowerStarAdjunction l p) (adicUpperStarLowerStarAdjunction l p')
    (adicUpperStar l g) (adicUpperStar l v)
    (adicUpperStarCompIso l sq.w.symm).symm
    (asIso (adicBaseChangeMap l sq.toCommSq.flip)) (heart_open_mate l sq.toCommSq)

/-- Normalize a factorization at a specified sheaf without unfolding the native functors. -/
@[irreducible] private def factor (l : ℕ) [Fact l.Prime] {P Q Z : Scheme.{u}}
    {a : P ⟶ Z} {b : P ⟶ Q} {c : Q ⟶ Z} (e : b ≫ c = a) (M : AdicSheaf l Z) :
    (adicUpperStar l a).obj M ≅
      (adicUpperStar l b).obj ((adicUpperStar l c).obj M) :=
  (adicUpperStarCongr l e.symm).app M ≪≫ (adicUpperStarComp l b c).app M

private theorem factor_rfl (l : ℕ) [Fact l.Prime] {P Q Z : Scheme.{u}}
    (b : P ⟶ Q) (c : Q ⟶ Z) (M : AdicSheaf l Z) :
    factor l (rfl : b ≫ c = b ≫ c) M = (adicUpperStarComp l b c).app M := by
  simp only [factor, adicUpperStarCongr, eqToIso_refl]
  exact Iso.refl_trans _

private theorem factor_assoc (l : ℕ) [Fact l.Prime] {P Q R Z : Scheme.{u}}
    {a : P ⟶ Z} {x : P ⟶ Q} {y : Q ⟶ R} {z : R ⟶ Z}
    {b : Q ⟶ Z} {c : P ⟶ R}
    (e_b : y ≫ z = b) (e_a : x ≫ b = a) (e_c : x ≫ y = c)
    (e_a' : c ≫ z = a) (M : AdicSheaf l Z) :
    (factor l e_a M).hom ≫ (adicUpperStar l x).map ((factor l e_b M).hom) =
      (factor l e_a' M).hom ≫
        (factor l e_c ((adicUpperStar l z).obj M)).hom := by
  subst e_b e_c e_a
  simp only [factor, adicUpperStarCongr, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    eqToHom_refl, NatTrans.id_app, Category.id_comp]
  rw [adicUpperStarComp_hom_app_comp_adicUpperStarComp_hom_app]
  simp only [adicUpperStarCongr, eqToIso.hom, eqToHom_refl, NatTrans.id_app,
    Category.id_comp]

private theorem factor_congr_right (l : ℕ) [Fact l.Prime] {P Q Z : Scheme.{u}}
    {a : P ⟶ Z} (x : P ⟶ Q) {b b' : Q ⟶ Z} (w : b = b')
    (e : x ≫ b = a) (e' : x ≫ b' = a) (M : AdicSheaf l Z) :
    (factor l e M).hom ≫ (adicUpperStar l x).map
        ((adicUpperStarCongr l w).hom.app M) = (factor l e' M).hom := by
  subst b'
  simp only [adicUpperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id ((factor l e M).hom)

private theorem factor_congr_left (l : ℕ) [Fact l.Prime] {P Q Z : Scheme.{u}}
    {a : P ⟶ Z} {x x' : P ⟶ Q} (b : Q ⟶ Z) (w : x = x')
    (e : x ≫ b = a) (e' : x' ≫ b = a) (M : AdicSheaf l Z) :
    (factor l e M).hom ≫
        (adicUpperStarCongr l w).hom.app ((adicUpperStar l b).obj M) =
      (factor l e' M).hom := by
  subst x'
  simp only [adicUpperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact Category.comp_id ((factor l e M).hom)

/-- The isomorphism between pullback along `m` and iterated pullback along `c`, `b` and `a`,
for a factorization `a ≫ (b ≫ c) = m`. -/
@[irreducible] private def triple (l : ℕ) [Fact l.Prime] {P Q R Z : Scheme.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ Z) {m : P ⟶ Z}
    (e : a ≫ (b ≫ c) = m) (M : AdicSheaf l Z) :
    (adicUpperStar l m).obj M ≅
      (adicUpperStar l a).obj ((adicUpperStar l b).obj ((adicUpperStar l c).obj M)) :=
  (factor l e M) ≪≫
    (adicUpperStar l a).mapIso ((adicUpperStarComp l b c).app M)

private theorem triple_assoc (l : ℕ) [Fact l.Prime] {P Q R Z : Scheme.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ Z) {m : P ⟶ Z}
    (e : a ≫ (b ≫ c) = m) (e' : (a ≫ b) ≫ c = m) (M : AdicSheaf l Z) :
    (triple l a b c e M).hom = (factor l e' M).hom ≫
      (adicUpperStarComp l a b).hom.app ((adicUpperStar l c).obj M) := by
  simpa only [triple, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, factor_rfl] using
    factor_assoc l rfl e rfl e' M

private theorem triple_inner (l : ℕ) [Fact l.Prime] {P Q R R' Z : Scheme.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ Z) (b' : Q ⟶ R') (c' : R' ⟶ Z)
    {m : P ⟶ Z} (w : b ≫ c = b' ≫ c')
    (e : a ≫ (b ≫ c) = m) (e' : a ≫ (b' ≫ c') = m) (M : AdicSheaf l Z) :
    (triple l a b c e M).hom ≫
        (adicUpperStar l a).map ((adicUpperStarCompIso l w).hom.app M) =
      (triple l a b' c' e' M).hom := by
  simp only [triple, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    adicUpperStarCompIso, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← Category.assoc, factor_congr_right l a w e e']

private theorem triple_outer (l : ℕ) [Fact l.Prime] {P Q Q' R Z : Scheme.{u}}
    (a : P ⟶ Q) (b : Q ⟶ R) (a' : P ⟶ Q') (b' : Q' ⟶ R) (c : R ⟶ Z)
    {m : P ⟶ Z} (w : a ≫ b = a' ≫ b')
    (e : a ≫ (b ≫ c) = m) (e' : a' ≫ (b' ≫ c) = m) (M : AdicSheaf l Z) :
    (triple l a b c e M).hom ≫
        (adicUpperStarCompIso l w).hom.app ((adicUpperStar l c).obj M) =
      (triple l a' b' c e' M).hom := by
  have eL : (a ≫ b) ≫ c = m := (Category.assoc a b c).trans e
  have eR : (a' ≫ b') ≫ c = m := (Category.assoc a' b' c).trans e'
  rw [triple_assoc l a b c e eL, triple_assoc l a' b' c e' eR]
  simp only [adicUpperStarCompIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, factor_congr_left l c w eL eR]

private theorem square_symm (l : ℕ) [Fact l.Prime] {P Q R Z : Scheme.{u}}
    {a : P ⟶ Q} {b : Q ⟶ Z} {c : P ⟶ R} {d : R ⟶ Z}
    (w : a ≫ b = c ≫ d) :
    adicUpperStarCompIso l w.symm = (adicUpperStarCompIso l w).symm := by
  have he : adicUpperStarCongr l w.symm = (adicUpperStarCongr l w).symm := by
    unfold adicUpperStarCongr
    exact transport_symm (congrArg (fun f : P ⟶ Z => adicUpperStar l f) w)
  simp only [adicUpperStarCompIso, he, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]

private theorem heart_pull_cube (l : ℕ) [Fact l.Prime]
    {X' X Y' Y XA XB A B : Scheme.{u}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {k : XA ⟶ X} {pA : XA ⟶ A} {t : XB ⟶ X'} {r : XB ⟶ XA}
    {q : XB ⟶ B} {i : A ⟶ Y} {j : B ⟶ Y'} {h : B ⟶ A}
    (s : CommSq v p' p g) (s' : CommSq r q pA h)
    (sF : CommSq k pA p i) (sG : CommSq h j i g)
    (sH : CommSq t r v k) (sK : CommSq t q p' j) (M : AdicSheaf l Y) :
    (adicUpperStar l q).map ((adicUpperStarCompIso l sG.w).hom.app M) ≫
      (adicUpperStarCompIso l sK.w.symm).hom.app ((adicUpperStar l g).obj M) ≫
      (adicUpperStar l t).map ((adicUpperStarCompIso l s.w.symm).hom.app M) =
    (adicUpperStarCompIso l s'.w.symm).hom.app ((adicUpperStar l i).obj M) ≫
      (adicUpperStar l r).map ((adicUpperStarCompIso l sF.w.symm).hom.app M) ≫
      (adicUpperStarCompIso l sH.w.symm).hom.app ((adicUpperStar l p).obj M) := by
  let m := q ≫ (h ≫ i)
  have e1 : q ≫ (j ≫ g) = m := by dsimp [m]; rw [← sG.w]
  have e2 : t ≫ (p' ≫ g) = m := by
    rw [← Category.assoc, sK.w, Category.assoc]
    exact e1
  have e3 : t ≫ (v ≫ p) = m := by rw [s.w]; exact e2
  have e4 : r ≫ (pA ≫ i) = m := by
    rw [← Category.assoc, s'.w, Category.assoc]
  have e5 : r ≫ (k ≫ p) = m := by rw [sF.w]; exact e4
  apply (cancel_epi (triple l q h i rfl M).hom).mp
  rw [reassoc_of% triple_inner l q h i j g sG.w rfl e1 M,
    reassoc_of% triple_outer l q j t p' g sK.w.symm e1 e2 M,
    triple_inner l t p' g v p s.w.symm e2 e3 M,
    reassoc_of% triple_outer l q h r pA i s'.w.symm rfl e4 M,
    reassoc_of% triple_inner l r pA i k p sF.w.symm e4 e5 M,
    triple_outer l r k t v p sH.w.symm e5 e3 M]

private theorem pull_cube (l : ℕ) [Fact l.Prime]
    {X' X Y' Y XA XB A B : Scheme.{u}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    {k : XA ⟶ X} {pA : XA ⟶ A} {t : XB ⟶ X'} {r : XB ⟶ XA}
    {q : XB ⟶ B} {i : A ⟶ Y} {j : B ⟶ Y'} {h : B ⟶ A}
    (s : CommSq v p' p g) (s' : CommSq r q pA h)
    (sF : CommSq k pA p i) (sG : CommSq h j i g)
    (sH : CommSq t r v k) (sK : CommSq t q p' j)
    (M : DerivedCategory (AdicSheaf l Y)) :
    (adicUpperStar l q).mapDerivedCategory.map
        ((adicDerivedPullSquare l sG).inv.app M) ≫
      (adicDerivedPullSquare l sK).hom.app ((adicUpperStar l g).mapDerivedCategory.obj M) ≫
      (adicUpperStar l t).mapDerivedCategory.map
        ((adicDerivedPullSquare l s).hom.app M) =
    (adicDerivedPullSquare l s').hom.app ((adicUpperStar l i).mapDerivedCategory.obj M) ≫
      (adicUpperStar l r).mapDerivedCategory.map
        ((adicDerivedPullSquare l sF).hom.app M) ≫
      (adicDerivedPullSquare l sH).hom.app ((adicUpperStar l p).mapDerivedCategory.obj M) := by
  have hc := Functor.mapDerivedCategory_exactCube
    (adicUpperStar l i) (adicUpperStar l h) (adicUpperStar l q)
    (adicUpperStar l g) (adicUpperStar l j) (adicUpperStar l p') (adicUpperStar l t)
    (adicUpperStar l p) (adicUpperStar l v) (adicUpperStar l pA)
    (adicUpperStar l r) (adicUpperStar l k)
    (adicUpperStarCompIso l sG.w) (adicUpperStarCompIso l sK.w.symm)
    (adicUpperStarCompIso l s.w.symm) (adicUpperStarCompIso l s'.w.symm)
    (adicUpperStarCompIso l sF.w.symm) (adicUpperStarCompIso l sH.w.symm)
    (heart_pull_cube l s s' sF sG sH sK)
  rw [square_symm l sG.w.symm] at hc
  simpa only [adicDerivedPullSquare, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] using
    NatTrans.congr_app hc M

/-- The pullback square over a further base map h, with all projections specified. -/
theorem adicChartSquare {X Y A B : Scheme.{u}} (p : X ⟶ Y) (i : A ⟶ Y) (h : B ⟶ A) :
    CommSq (pullback.fst (pullback.snd p i) h) (pullback.snd (pullback.snd p i) h)
      (pullback.snd p i) h :=
  ⟨pullback.condition⟩

/-- Restriction of the specified global mate is isomorphic as an arrow to its chart mate. -/
theorem adicDerivedBaseChange_openChart (l : ℕ) [Fact l.Prime]
    {X' X Y' Y A B : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback v p' p g)
    (i : A ⟶ Y) (j : B ⟶ Y') [IsOpenImmersion i] [IsOpenImmersion j]
    (h : B ⟶ A) (w : h ≫ i = j ≫ g)
    (M : DerivedCategory (AdicSheaf l X)) :
    Nonempty (Arrow.mk ((adicUpperStar l j).mapDerivedCategory.map
        ((adicDerivedBaseChange l sq.toCommSq).app M)) ≅
      Arrow.mk ((adicDerivedBaseChange l (adicChartSquare p i h)).app
        ((adicUpperStar l (pullback.fst p i)).mapDerivedCategory.obj M))) := by
  let k := pullback.fst p i
  let pA := pullback.snd p i
  let r := pullback.fst pA h
  let q := pullback.snd pA h
  have sF : IsPullback k pA p i := IsPullback.of_hasPullback p i
  have s' : IsPullback r q pA h := IsPullback.of_hasPullback pA h
  have hw : (r ≫ k) ≫ p = (q ≫ j) ≫ g := by
    rw [Category.assoc, sF.w, ← Category.assoc r, s'.w, Category.assoc, w,
      Category.assoc]
  let t := sq.lift (r ≫ k) (q ≫ j) hw
  have htv : t ≫ v = r ≫ k := sq.lift_fst _ _ _
  have htp : t ≫ p' = q ≫ j := sq.lift_snd _ _ _
  have sH : CommSq t r v k := ⟨htv⟩
  have sG : CommSq h j i g := ⟨w⟩
  have sK : IsPullback t q p' j := by
    apply IsPullback.of_right (t := sq) (p := htp)
    rw [htv, ← w]
    exact s'.paste_horiz sF
  have : IsOpenImmersion t := MorphismProperty.of_isPullback sK.flip inferInstance
  let pF := (adicDerivedPullSquare l sF.toCommSq).symm
  let pG := adicDerivedPullSquare l sG
  let pH := (adicDerivedPullSquare l sH).symm
  let pK := (adicDerivedPullSquare l sK.toCommSq).symm
  have hF : IsIso (adicDerivedBaseChange l sF.toCommSq) := by
    rw [derived_open_mate l sF]
    infer_instance
  have hK : IsIso (adicDerivedBaseChange l sK.toCommSq) := by
    rw [derived_open_mate l sK]
    infer_instance
  let a := pG.app ((adicLowerStar l p).rightDerivedFunctor.obj M) ≪≫
    (adicUpperStar l h).mapDerivedCategory.mapIso
      ((asIso (adicDerivedBaseChange l sF.toCommSq)).app M)
  let b := (asIso (adicDerivedBaseChange l sK.toCommSq)).app
      ((adicUpperStar l v).mapDerivedCategory.obj M) ≪≫
    (adicLowerStar l q).rightDerivedFunctor.mapIso (pH.app M)
  refine ⟨Arrow.isoMk a b ?_⟩
  have hc := exchangeMate_cube
    (adicUpperStarLowerStarAdjunction l p).mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStarLowerStarAdjunction l p').mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStarLowerStarAdjunction l pA).mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStarLowerStarAdjunction l q).mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStar l i).mapDerivedCategory (adicUpperStar l k).mapDerivedCategory
    (adicUpperStar l j).mapDerivedCategory (adicUpperStar l t).mapDerivedCategory
    pF pG pH pK (adicDerivedPullSquare l sq.toCommSq).hom
    (adicDerivedPullSquare l s'.toCommSq).hom
    (pull_cube l sq.toCommSq s'.toCommSq sF.toCommSq sG sH sK.toCommSq) M
  simpa only [a, b, pF, pG, pH, pK, adicDerivedBaseChange,
    Iso.trans_hom, Iso.symm_inv, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
    Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc] using hc.symm

end AlgebraicGeometry.ProEtale
