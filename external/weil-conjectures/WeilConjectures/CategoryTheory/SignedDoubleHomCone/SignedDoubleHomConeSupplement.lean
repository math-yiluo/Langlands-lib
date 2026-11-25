/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
public import WeilConjectures.Algebra.Homology.SignedDoubleHomCone

/-!
# Signed double internal Hom and mapping cones

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08JC;
derived.tex, Definition 014E (blueprint: lem-sf-double-hom-cone-comparison).
The component equations below are equations of module sheaves, hence include every
local section and all restriction maps. Mathlib orders the cone summands as A[1], B.
-/

@[expose] public section

set_option linter.unusedSectionVars false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] CategoryTheory.homComplexFunctor

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SignedDoubleHomCone

namespace Calculation

-- Work through the projection API in an arbitrary preadditive category.
-- This keeps the component calculations independent of the sheaf implementation.

universe u' v'
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]

private structure HomData (D : Type u') [Category.{v'} D] [Preadditive D] where
  obj : D → D → D
  map : ∀ {A A' B B' : D}, (A' ⟶ A) → (B ⟶ B') → (obj A B ⟶ obj A' B')
  map_id : ∀ (A B : D), map (𝟙 A) (𝟙 B) = 𝟙 (obj A B)
  map_comp : ∀ {A A' A'' B B' B'' : D}
    (f : A' ⟶ A) (f' : A'' ⟶ A') (g : B ⟶ B') (g' : B' ⟶ B''),
    map f g ≫ map f' g' = map (f' ≫ f) (g ≫ g')
  map_add_left : ∀ {A A' B B' : D} (f g : A' ⟶ A) (h : B ⟶ B'),
    map (f + g) h = map f h + map g h
  map_zero_left : ∀ {A A' B B' : D} (g : B ⟶ B'), map (0 : A' ⟶ A) g = 0

omit [HasBinaryBiproducts D] in
private lemma map_neg_left {H : HomData D} {A A' B B' : D}
    (f : A' ⟶ A) (g : B ⟶ B') : H.map (-f) g = -H.map f g := by
  apply eq_neg_of_add_eq_zero_left
  erw [← H.map_add_left, neg_add_cancel, H.map_zero_left]

omit [HasBinaryBiproducts D] in
private lemma map_smul_left {H : HomData D} {A A' B B' : D}
    (e : ℤˣ) (f : A' ⟶ A) (g : B ⟶ B') :
    H.map (e • f) g = e • H.map f g := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul]
    exact map_neg_left f g

private noncomputable abbrev coneMap {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b) :=
  CochainComplex.mappingCone.map a.hom b.hom h.left h.right h.w.symm

private abbrev hc
    (F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (K I : CochainComplex D ℤ) := (F.obj (op K)).obj I

private structure Spec (H : HomData D)
    (F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ) where
  π : ∀ (K I : CochainComplex D ℤ) (n a b : ℤ) (_h : a + n = b),
    ((F.obj (op K)).obj I).X n ⟶ H.obj (K.X a) (I.X b)
  lim : ∀ (K I : CochainComplex D ℤ) (n : ℤ),
    IsLimit (Fan.mk (((F.obj (op K)).obj I).X n) (fun a : ℤ ↦ π K I n a (a + n) rfl))
  diff : ∀ (K I : CochainComplex D ℤ) (n m a b b' a' : ℤ)
    (_hnm : n + 1 = m) (h : a + m = b) (h' : a + n = b') (ha' : a' + n = b),
    ((F.obj (op K)).obj I).d n m ≫ π K I m a b h =
      π K I n a b' h' ≫ H.map (𝟙 _) (I.d b' b) -
      n.negOnePow • (π K I n a' b ha' ≫
        H.map (K.d a a') (𝟙 _))
  map : ∀ (L L' M M' : CochainComplex D ℤ) (f : L' ⟶ L) (g : M ⟶ M')
    (n a b : ℤ) (h : a + n = b),
    (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n a b h =
      π L M n a b h ≫ H.map (f.f a) (g.f b)

variable {F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ}

private noncomputable def productLimit {H : HomData D} (P : Spec H F)
    (K I : CochainComplex D ℤ) (n : ℤ) :
    IsLimit (Fan.mk ((hc F K I).X n) (fun a : ℤ ↦ P.π K I n a (a + n) rfl)) :=
  P.lim K I n

private abbrev dualF
    (F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤
      CochainComplex D ℤ) (I : CochainComplex D ℤ) :
    (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ where
  obj K := hc F K.unop I
  map f := (F.map f).app I
  map_id K := by simp only [Functor.map_id, NatTrans.id_app]
  map_comp f g := by simp only [Functor.map_comp, NatTrans.comp_app]

private abbrev doubleDualF
    (F : (CochainComplex D ℤ)ᵒᵖ ⥤ CochainComplex D ℤ ⥤
      CochainComplex D ℤ) (I : CochainComplex D ℤ) :
    CochainComplex D ℤ ⥤ CochainComplex D ℤ where
  obj K := hc F (hc F K I) I
  map f := (dualF F I).map ((dualF F I).map f.op).op
  map_id K := by simp only [Functor.map_id, NatTrans.id_app, op_id]
  map_comp f g := by simp only [Functor.map_comp, NatTrans.comp_app, op_comp]

private noncomputable def inB {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (q : ℤ) :
    (hc F B I).X q ⟶ (hc F (HomologicalComplex.homotopyCofiber f) I).X q :=
  Fan.IsLimit.lift (productLimit P _ I q) (fun a : ℤ ↦
    P.π B I q a (a + q) rfl ≫
      H.map (HomologicalComplex.homotopyCofiber.sndX f a) (𝟙 _))

private noncomputable def inA {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (t : ℤ) :
    (hc F A I).X t ⟶ (hc F (HomologicalComplex.homotopyCofiber f) I).X (t + 1) :=
  Fan.IsLimit.lift (productLimit P _ I (t + 1)) (fun a : ℤ ↦
    P.π A I t (a + 1) (a + (t + 1)) (by omega) ≫
      H.map
        (HomologicalComplex.homotopyCofiber.fstX f a (a + 1) rfl) (𝟙 _))

private noncomputable def reindexOne {H : HomData D} (P : Spec H F)
    (K I : CochainComplex D ℤ) (t : ℤ) :
    (hc F K I).X t ⟶ (hc F (K⟦(1 : ℤ)⟧) I).X (t + 1) :=
  Fan.IsLimit.lift (productLimit P _ I (t + 1)) (fun a : ℤ ↦
    P.π K I t (a + 1) (a + (t + 1)) (by omega) ≫
      H.map (K.shiftFunctorObjXIso 1 a (a + 1) rfl).hom (𝟙 _))

omit [HasBinaryBiproducts D] in
private lemma proj_ext {H : HomData D} (P : Spec H F) (K I : CochainComplex D ℤ) (n : ℤ)
    {Z : D} {f g : Z ⟶ (hc F K I).X n}
    (h : ∀ a, f ≫ P.π K I n a (a + n) rfl = g ≫ P.π K I n a (a + n) rfl) :
    f = g := Fan.IsLimit.hom_ext (productLimit P K I n) f g h

omit [HasBinaryBiproducts D] in
private lemma d_proj {H : HomData D} (P : Spec H F) (K I : CochainComplex D ℤ)
    (n m a b b' a' : ℤ) (hnm : n + 1 = m) (h : a + m = b)
    (h' : a + n = b') (ha' : a' + n = b) :
    (hc F K I).d n m ≫ P.π K I m a b h =
      P.π K I n a b' h' ≫ H.map (𝟙 _) (I.d b' b) -
      n.negOnePow • (P.π K I n a' b ha' ≫
        H.map (K.d a a') (𝟙 _)) :=
  P.diff K I n m a b b' a' hnm h h' ha'

omit [HasBinaryBiproducts D] in
private lemma dual_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {K L : CochainComplex D ℤ} (f : K ⟶ L)
    (n a b : ℤ) (h : a + n = b) :
    ((dualF F I).map f.op).f n ≫ P.π K I n a b h =
      P.π L I n a b h ≫ H.map (f.f a) (𝟙 _) := by
  simpa only [Functor.map_id, HomologicalComplex.id_f, Category.comp_id,
    dualF, Functor.flip_obj_map] using P.map L K I I f (𝟙 I) n a b h

omit [HasBinaryBiproducts D] in
private lemma proj_eq {H : HomData D} (P : Spec H F) (K I : CochainComplex D ℤ) (n a a' b : ℤ)
    (h : a' = a) (hb : a + n = b) :
    P.π K I n a' b (by omega) ≫
        H.map (K.XIsoOfEq h).inv (𝟙 _) = P.π K I n a b hb := by
  subst a'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    H.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
-- Step 1: signed reindexing, its inverse and naturality.
private lemma shift_exists {H : HomData D} (P : Spec H F) (I K : CochainComplex D ℤ) (m : ℤ) :
    ∃ s : hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧,
      ∀ (q a : ℤ),
        s.hom.f q ≫
            ((hc F K I).shiftFunctorObjXIso (-m) q (q - m) (by omega)).hom ≫
            P.π K I (q - m) (a + m) (a + q) (by omega) =
          (m * q).negOnePow • (P.π (K⟦m⟧) I q a (a + q) rfl ≫
            H.map (K.shiftFunctorObjXIso m a (a + m) rfl).inv
              (𝟙 _)) := by
  classical
  let S := K⟦m⟧
  let U := (hc F K I)⟦-m⟧
  let V := hc F S I
  let a (n : ℤ) : U.X n ⟶ V.X n :=
    Fan.IsLimit.lift (productLimit P S I n) (fun p ↦
      (m * n).negOnePow • P.π K I (n - m) (p + m) (p + n) (by omega))
  have ha (n p q : ℤ) (h : p + n = q) :
      a n ≫ P.π S I n p q h =
        (m * n).negOnePow • P.π K I (n - m) (p + m) q (by omega) := by
    subst q
    exact Fan.IsLimit.fac (productLimit P S I n) _ p
  let b (n : ℤ) : V.X n ⟶ U.X n :=
    Fan.IsLimit.lift (productLimit P K I (n - m)) (fun p ↦
      (m * n).negOnePow • (P.π S I n (p - m) (p + (n - m)) (by omega) ≫
        H.map
          (K.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)))
  have hb (n p q : ℤ) (h : p + (n - m) = q) :
      b n ≫ P.π K I (n - m) p q h =
        (m * n).negOnePow • (P.π S I n (p - m) q (by omega) ≫
          H.map (K.XIsoOfEq (show p - m + m = p by omega)).inv
            (𝟙 _)) := by
    subst q
    exact Fan.IsLimit.fac (productLimit P K I (n - m)) _ p
  have hab (n : ℤ) : a n ≫ b n = 𝟙 _ := by
    apply proj_ext P K I (n - m)
    intro p
    dsimp only [U, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    erw [Category.assoc, hb, Linear.comp_units_smul, ← Category.assoc, ha]
    simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul]
    simp only [Category.id_comp]
    change _ = P.π K I (n - m) p (p + (n - m)) rfl
    exact proj_eq P K I (n - m) p (p - m + m) _ (by omega) rfl
  have hba (n : ℤ) : b n ≫ a n = 𝟙 _ := by
    apply proj_ext P S I n
    intro p
    dsimp only [U, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    erw [Category.assoc, ha, Linear.comp_units_smul, hb]
    simp only [smul_smul, Int.units_mul_self, one_smul]
    simp only [Category.id_comp]
    change _ = P.π S I n p (p + n) rfl
    exact proj_eq P S I n p (p + m - m) _ (by omega) rfl
  let e (n : ℤ) : U.X n ≅ V.X n := ⟨a n, b n, hab n, hba n⟩
  have hc (n k : ℤ) (h : n + 1 = k) :
      (e n).hom ≫ V.d n k = U.d n k ≫ (e k).hom := by
    subst k
    dsimp only [U, CochainComplex.shiftFunctor_obj_X'] at a ha ⊢
    apply proj_ext P S I (n + 1)
    intro p
    change (a n ≫ V.d n (n + 1)) ≫ P.π S I (n + 1) p (p + (n + 1)) rfl =
      (((-m).negOnePow • (hc F K I).d (n - m) (n + 1 - m)) ≫
        a (n + 1)) ≫ P.π S I (n + 1) p (p + (n + 1)) rfl
    erw [Category.assoc,
      d_proj P S I n (n + 1) p (p + (n + 1)) (p + n) (p + 1)
        rfl rfl rfl (by omega),
      Preadditive.comp_sub, Linear.comp_units_smul, ← Category.assoc,
      ha n p (p + n) rfl, ← Category.assoc,
      ha n (p + 1) (p + (n + 1)) (by omega), Category.assoc]
    conv_rhs => erw [ha (n + 1) p (p + (n + 1)) rfl]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
    erw [d_proj P K I (n - m) (n + 1 - m) (p + m) (p + (n + 1)) (p + n) (p + 1 + m)
        (by omega) (by omega) (by omega) (by omega)]
    dsimp only [S, CochainComplex.shiftFunctor_obj_d']
    erw [map_smul_left]
    simp only [Linear.comp_units_smul, smul_sub, smul_smul,
      Int.negOnePow_neg, Int.negOnePow_sub]
    have hs : (m * (n + 1)).negOnePow = (m * n).negOnePow * m.negOnePow := by
      erw [mul_add, mul_one, Int.negOnePow_add]
    simp only [hs, mul_assoc, Int.units_mul_self, mul_one]
    erw [mul_left_comm n.negOnePow (m * n).negOnePow m.negOnePow]
    rfl
  let s := (HomologicalComplex.Hom.isoOfComponents e hc).symm
  refine ⟨s, ?_⟩
  intro q p
  dsimp only [s, HomologicalComplex.Hom.isoOfComponents, Iso.symm_hom,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  dsimp only [CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_X]
  simp only [Category.id_comp]
  change b q ≫ P.π K I (q - m) (p + m) (p + q) (by omega) = _
  erw [hb]
  simp only [Iso.refl_inv]
  congr 1
  simpa only [H.map_id, Category.comp_id, S, HomologicalComplex.XIsoOfEq,
    CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_X] using
    (proj_eq P S I q p (p + m - m) _ (by omega) rfl)

private lemma shift_natural {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    (s : ∀ (K : CochainComplex D ℤ) (m : ℤ),
      hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧)
    (hs : ∀ (K : CochainComplex D ℤ) (m q a : ℤ),
      (s K m).hom.f q ≫ P.π K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • P.π (K⟦m⟧) I q a (a + q) rfl)
    {K L : CochainComplex D ℤ} (f : K ⟶ L) (m : ℤ) :
    (dualF F I).map (f⟦m⟧').op ≫ (s K m).hom =
      (s L m).hom ≫ ((dualF F I).map f.op)⟦-m⟧' := by
  apply HomologicalComplex.hom_ext
  intro q
  change ((dualF F I).map (f⟦m⟧').op).f q ≫ (s K m).hom.f q =
    (s L m).hom.f q ≫ ((dualF F I).map f.op).f (q - m)
  apply proj_ext P K I (q - m)
  intro a
  obtain ⟨a, rfl⟩ : ∃ z : ℤ, z + m = a := ⟨a - m, by omega⟩
  have hs' (D : CochainComplex D ℤ) (b : ℤ) (hb : a + q = b) :
      (s D m).hom.f q ≫ P.π D I (q - m) (a + m) b (by omega) =
        (m * q).negOnePow • P.π (D⟦m⟧) I q a b hb := by
    subst b
    exact hs D m q a
  erw [Category.assoc, hs' K _ (by omega), Linear.comp_units_smul, dual_proj P,
    Category.assoc, dual_proj P, ← Category.assoc, hs' L _ (by omega),
    Linear.units_smul_comp]
  rfl

private lemma inB_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (q a b : ℤ) (h : a + q = b) :
    inB P I f q ≫ P.π (HomologicalComplex.homotopyCofiber f) I q a b h =
      P.π B I q a b h ≫
        H.map (HomologicalComplex.homotopyCofiber.sndX f a) (𝟙 _) := by
  subst b
  exact Fan.IsLimit.fac (productLimit P _ I q) _ a

private lemma inA_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (t a a' b : ℤ) (ha : a + 1 = a') (hb : a + (t + 1) = b) :
    inA P I f t ≫ P.π (HomologicalComplex.homotopyCofiber f) I (t + 1) a b hb =
      P.π A I t a' b (by omega) ≫
        H.map
          (HomologicalComplex.homotopyCofiber.fstX f a a' ha) (𝟙 _) := by
  subst a' b
  exact Fan.IsLimit.fac (productLimit P _ I (t + 1)) _ a

-- Step 3: the two unsigned summands of Hom(Cone(f), I).
private noncomputable def outB {H : HomData D} (_P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (q : ℤ) :
    (hc F (HomologicalComplex.homotopyCofiber f) I).X q ⟶ (hc F B I).X q :=
  ((dualF F I).map (CochainComplex.mappingCone.inr f).op).f q

private lemma outB_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (q a b : ℤ) (h : a + q = b) :
    outB P I f q ≫ P.π B I q a b h =
      P.π (HomologicalComplex.homotopyCofiber f) I q a b h ≫
        H.map (HomologicalComplex.homotopyCofiber.inrX f a) (𝟙 _) := by
  exact dual_proj P I (CochainComplex.mappingCone.inr f) q a b h

private noncomputable def outA {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (q t : ℤ) (h : t + 1 = q) :
    (hc F (HomologicalComplex.homotopyCofiber f) I).X q ⟶ (hc F A I).X t :=
  Fan.IsLimit.lift (productLimit P A I t) (fun a ↦
    P.π (HomologicalComplex.homotopyCofiber f) I q (a - 1) (a + t) (by omega) ≫
      H.map
        (HomologicalComplex.homotopyCofiber.inlX f a (a - 1) (by
          change a - 1 + 1 = a
          omega)) (𝟙 _))

private lemma outA_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (q t : ℤ) (h : t + 1 = q) (a a' b : ℤ)
    (ha : a' + 1 = a) (hb : a + t = b) :
    outA P I f q t h ≫ P.π A I t a b hb =
      P.π (HomologicalComplex.homotopyCofiber f) I q a' b (by omega) ≫
        H.map
          (HomologicalComplex.homotopyCofiber.inlX f a a' ha) (𝟙 _) := by
  obtain rfl : a' = a - 1 := by omega
  subst b
  exact Fan.IsLimit.fac (productLimit P A I t) _ a

private lemma inB_outB {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (q : ℤ) :
    inB P I f q ≫ outB P I f q = 𝟙 _ := by
  apply proj_ext P B I q
  intro a
  erw [Category.assoc, outB_proj P, ← Category.assoc, inB_proj P, Category.assoc]
  simp only [H.map_comp,
    HomologicalComplex.homotopyCofiber.inrX_sndX, Category.id_comp,
    H.map_id, Category.comp_id]

private lemma inA_outB {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (t : ℤ) :
    inA P I f t ≫ outB P I f (t + 1) = 0 := by
  apply proj_ext P B I (t + 1)
  intro a
  erw [Category.assoc, outB_proj P, ← Category.assoc,
    inA_proj P I f t a (a + 1) _ rfl rfl, Category.assoc]
  simp only [H.map_comp,
    HomologicalComplex.homotopyCofiber.inrX_fstX, Category.id_comp,
    CategoryTheory.Limits.zero_comp]
  erw [H.map_zero_left]
  exact CategoryTheory.Limits.comp_zero

private lemma inB_outA {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (t : ℤ) :
    inB P I f (t + 1) ≫ outA P I f (t + 1) t rfl = 0 := by
  apply proj_ext P A I t
  intro a
  erw [Category.assoc, outA_proj P I f (t + 1) t rfl a (a - 1) _ (by omega) rfl,
    ← Category.assoc, inB_proj P, Category.assoc]
  simp only [H.map_comp,
    HomologicalComplex.homotopyCofiber.inlX_sndX, Category.id_comp,
    CategoryTheory.Limits.zero_comp]
  erw [H.map_zero_left]
  exact CategoryTheory.Limits.comp_zero

private lemma inA_outA {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (t : ℤ) :
    inA P I f t ≫ outA P I f (t + 1) t rfl = 𝟙 _ := by
  apply proj_ext P A I t
  intro a
  obtain ⟨a, rfl⟩ : ∃ z : ℤ, z + 1 = a := ⟨a - 1, by omega⟩
  erw [Category.assoc, outA_proj P I f (t + 1) t rfl (a + 1) a _ rfl rfl,
    ← Category.assoc, inA_proj P I f t a (a + 1) _ rfl (by omega), Category.assoc]
  simp only [H.map_comp,
    HomologicalComplex.homotopyCofiber.inlX_fstX, Category.id_comp,
    H.map_id, Category.comp_id]

private lemma out_in_sum {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (t : ℤ) :
    outB P I f (t + 1) ≫ inB P I f (t + 1) +
      outA P I f (t + 1) t rfl ≫ inA P I f t = 𝟙 _ := by
  apply proj_ext P (HomologicalComplex.homotopyCofiber f) I (t + 1)
  intro a
  simp only [Preadditive.add_comp, Category.assoc]
  erw [inB_proj P, inA_proj P I f t a (a + 1) _ rfl rfl]
  erw [← Category.assoc, outB_proj P]
  conv_lhs => rhs; erw [← Category.assoc,
    outA_proj P I f (t + 1) t rfl (a + 1) a _ rfl (by omega)]
  simp only [Category.assoc, H.map_comp, Category.id_comp]
  have hc : HomologicalComplex.homotopyCofiber.sndX f a ≫
        HomologicalComplex.homotopyCofiber.inrX f a +
      HomologicalComplex.homotopyCofiber.fstX f a (a + 1) rfl ≫
        HomologicalComplex.homotopyCofiber.inlX f (a + 1) a rfl = 𝟙 _ := by
    apply HomologicalComplex.homotopyCofiber.ext_to_X f a (a + 1) rfl
    · simp only [Preadditive.add_comp, Category.assoc,
        HomologicalComplex.homotopyCofiber.inrX_fstX, comp_zero,
        HomologicalComplex.homotopyCofiber.inlX_fstX, Category.comp_id,
        zero_add, Category.id_comp]
    · simp only [Preadditive.add_comp, Category.assoc,
        HomologicalComplex.homotopyCofiber.inrX_sndX, Category.comp_id,
        HomologicalComplex.homotopyCofiber.inlX_sndX, comp_zero,
        add_zero, Category.id_comp]
  erw [← Preadditive.comp_add, ← H.map_add_left, hc]
  erw [H.map_id]
  exact Category.comp_id _

private lemma inA_d {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (t : ℤ) :
    inA P I f t ≫ (hc F (HomologicalComplex.homotopyCofiber f) I).d (t + 1) (t + 1 + 1) =
      (hc F A I).d t (t + 1) ≫ inA P I f (t + 1) := by
  apply proj_ext P (HomologicalComplex.homotopyCofiber f) I (t + 1 + 1)
  intro a
  erw [Category.assoc,
    d_proj P _ I (t + 1) (t + 1 + 1) a (a + (t + 1 + 1)) (a + (t + 1)) (a + 1)
      (by omega) rfl rfl (by omega),
    Preadditive.comp_sub, Linear.comp_units_smul, ← Category.assoc,
    inA_proj P I f t a (a + 1) _ rfl rfl, Category.assoc,
    H.map_comp, Category.id_comp]
  erw [← Category.assoc, inA_proj P I f t (a + 1) (a + 2) _ (by omega) (by omega),
    Category.assoc, H.map_comp, Category.id_comp]
  erw [HomologicalComplex.homotopyCofiber_d,
    HomologicalComplex.homotopyCofiber.d_fstX f a (a + 1) (a + 2)
    rfl (show (ComplexShape.up ℤ).Rel (a + 1) (a + 2) by
      change a + 1 + 1 = a + 2
      omega), map_neg_left]
  simp only [Preadditive.comp_neg, smul_neg, sub_neg_eq_add,
    Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, Units.neg_smul]
  simp only [Category.assoc]
  erw [inA_proj P I f (t + 1) a (a + 1) _ rfl (by omega),
    ← Category.assoc,
    d_proj P A I t (t + 1) (a + 1) (a + (t + 1 + 1)) (a + (t + 1)) (a + 2)
      rfl (by omega) (by omega) (by omega)]
  simp only [Linear.units_smul_comp, Category.assoc,
    H.map_comp, Category.comp_id,
    Preadditive.add_comp, Preadditive.neg_comp, sub_eq_add_neg,
    HomologicalComplex.homotopyCofiber.fstX]

private lemma inB_d {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (q : ℤ) :
    inB P I f q ≫ (hc F (HomologicalComplex.homotopyCofiber f) I).d q (q + 1) =
      (hc F B I).d q (q + 1) ≫ inB P I f (q + 1) +
        (q + 1).negOnePow •
          (((((dualF F I).map f.op) : hc F B I ⟶ hc F A I)).f q ≫ inA P I f q) := by
  apply proj_ext P (HomologicalComplex.homotopyCofiber f) I (q + 1)
  intro a
  erw [Category.assoc,
    d_proj P _ I q (q + 1) a (a + (q + 1)) (a + q) (a + 1)
      rfl rfl rfl (by omega),
    Preadditive.comp_sub, Linear.comp_units_smul, ← Category.assoc,
    inB_proj P, Category.assoc, H.map_comp,
    Category.id_comp,
    ← Category.assoc, inB_proj P, Category.assoc,
    H.map_comp, Category.id_comp]
  erw [HomologicalComplex.homotopyCofiber_d,
    HomologicalComplex.homotopyCofiber.d_sndX f a (a + 1) rfl, H.map_add_left,
    Preadditive.comp_add, smul_add, sub_add_eq_sub_sub]
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
  erw [inB_proj P, ← Category.assoc,
    d_proj P B I q (q + 1) a (a + (q + 1)) (a + q) (a + 1)
      rfl rfl rfl (by omega)]
  erw [inA_proj P I f q a (a + 1) _ rfl rfl, ← Category.assoc,
    dual_proj P I f q (a + 1) _ (by omega)]
  simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
    H.map_comp,  Category.comp_id,
    Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, Units.neg_smul]
  abel

-- Steps 4 and 5: apply Hom again and insert the cone comparison sign.
private noncomputable def bidualB {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).X p ⟶
      (hc F (hc F B I) I).X p :=
  Fan.IsLimit.lift (productLimit P (hc F B I) I p) (fun q ↦
    P.π (hc F (HomologicalComplex.homotopyCofiber f) I) I p q (q + p) rfl ≫
      H.map (inB P I f q) (𝟙 _))

private lemma bidualB_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (p q b : ℤ) (h : q + p = b) :
    bidualB P I f p ≫ P.π (hc F B I) I p q b h =
      P.π (hc F (HomologicalComplex.homotopyCofiber f) I) I p q b h ≫
        H.map (inB P I f q) (𝟙 _) := by
  subst b
  exact Fan.IsLimit.fac (productLimit P (hc F B I) I p) _ q

private noncomputable def bidualA {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).X p ⟶
      (hc F (hc F A I) I).X (p + 1) :=
  Fan.IsLimit.lift (productLimit P (hc F A I) I (p + 1)) (fun t ↦
    (p + t).negOnePow •
      (P.π (hc F (HomologicalComplex.homotopyCofiber f) I) I p (t + 1)
        (t + (p + 1)) (by omega) ≫ H.map (inA P I f t) (𝟙 _)))

private lemma bidualA_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (p t b : ℤ) (hb : t + (p + 1) = b) :
    bidualA P I f p ≫ P.π (hc F A I) I (p + 1) t b hb =
      (p + t).negOnePow •
        (P.π (hc F (HomologicalComplex.homotopyCofiber f) I) I p (t + 1) b (by omega) ≫
          H.map (inA P I f t) (𝟙 _)) := by
  subst b
  exact Fan.IsLimit.fac (productLimit P (hc F A I) I (p + 1)) _ t

private noncomputable def bidualInvB {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (hc F (hc F B I) I).X p ⟶
      (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).X p :=
  Fan.IsLimit.lift (productLimit P (hc F (HomologicalComplex.homotopyCofiber f) I) I p)
    (fun q ↦ P.π (hc F B I) I p q (q + p) rfl ≫
      H.map (outB P I f q) (𝟙 _))

private lemma bidualInvB_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (p q b : ℤ) (h : q + p = b) :
    bidualInvB P I f p ≫
        P.π (hc F (HomologicalComplex.homotopyCofiber f) I) I p q b h =
      P.π (hc F B I) I p q b h ≫
        H.map (outB P I f q) (𝟙 _) := by
  subst b
  exact Fan.IsLimit.fac (productLimit P (hc F (HomologicalComplex.homotopyCofiber f) I) I p)
    _ q

private noncomputable def bidualInvA {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (hc F (hc F A I) I).X (p + 1) ⟶
      (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).X p :=
  Fan.IsLimit.lift (productLimit P (hc F (HomologicalComplex.homotopyCofiber f) I) I p)
    (fun q ↦ (p + (q - 1)).negOnePow •
      (P.π (hc F A I) I (p + 1) (q - 1) (q + p) (by omega) ≫
        H.map (outA P I f q (q - 1) (by omega)) (𝟙 _)))

private lemma bidualInvA_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B)
    (p q t b : ℤ) (ht : t + 1 = q) (hb : q + p = b) :
    bidualInvA P I f p ≫
        P.π (hc F (HomologicalComplex.homotopyCofiber f) I) I p q b hb =
      (p + t).negOnePow •
        (P.π (hc F A I) I (p + 1) t b (by omega) ≫
          H.map (outA P I f q t ht) (𝟙 _)) := by
  obtain rfl : t = q - 1 := by omega
  subst b
  exact Fan.IsLimit.fac (productLimit P (hc F (HomologicalComplex.homotopyCofiber f) I) I p)
    _ q

private lemma bidualInvB_B {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    bidualInvB P I f p ≫ bidualB P I f p = 𝟙 _ := by
  apply proj_ext P (hc F B I) I p
  intro q
  erw [Category.assoc, bidualB_proj P, ← Category.assoc, bidualInvB_proj P]
  simp only [Category.assoc, H.map_comp,
    inB_outB P, Category.id_comp, H.map_id, Category.comp_id]

private lemma bidualInvA_A {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    bidualInvA P I f p ≫ bidualA P I f p = 𝟙 _ := by
  apply proj_ext P (hc F A I) I (p + 1)
  intro t
  erw [Category.assoc, bidualA_proj P, Linear.comp_units_smul, ← Category.assoc,
    bidualInvA_proj P I f p (t + 1) t _ rfl (by omega)]
  simp only [Linear.units_smul_comp, Category.assoc,
    H.map_comp, inA_outA P, Category.id_comp,
    H.map_id, Category.comp_id, smul_smul,
    Int.units_mul_self, one_smul, Category.id_comp]

private lemma bidualInvB_A {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    bidualInvB P I f p ≫ bidualA P I f p = 0 := by
  apply proj_ext P (hc F A I) I (p + 1)
  intro t
  erw [Category.assoc, bidualA_proj P, Linear.comp_units_smul, ← Category.assoc,
    bidualInvB_proj P]
  simp only [Category.assoc, H.map_comp,
    inA_outB P, Category.id_comp, CategoryTheory.Limits.zero_comp]
  erw [H.map_zero_left]
  simp only [CategoryTheory.Limits.comp_zero, smul_zero]

private lemma bidualInvA_B {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    bidualInvA P I f p ≫ bidualB P I f p = 0 := by
  apply proj_ext P (hc F B I) I p
  intro q
  erw [Category.assoc, bidualB_proj P, ← Category.assoc,
    bidualInvA_proj P I f p q (q - 1) _ (by omega) rfl,
    Linear.units_smul_comp, Category.assoc]
  have hz (q t : ℤ) (h : t + 1 = q) :
      inB P I f q ≫ outA P I f q t h = 0 := by
    subst q
    exact inB_outA P I f t
  simp only [H.map_comp, hz, Category.id_comp,
    CategoryTheory.Limits.zero_comp]
  erw [H.map_zero_left]
  simp only [CategoryTheory.Limits.comp_zero, smul_zero]

private lemma bidual_sum {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    bidualB P I f p ≫ bidualInvB P I f p +
      bidualA P I f p ≫ bidualInvA P I f p = 𝟙 _ := by
  apply proj_ext P (hc F (HomologicalComplex.homotopyCofiber f) I) I p
  intro q
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, t + 1 = q := ⟨q - 1, by omega⟩
  simp only [Preadditive.add_comp, Category.assoc]
  erw [bidualInvB_proj P, bidualInvA_proj P I f p (t + 1) t _ rfl rfl,
    Linear.comp_units_smul, ← Category.assoc, bidualB_proj P]
  conv_lhs => rhs; erw [← Category.assoc, bidualA_proj P]
  simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul,
    Category.assoc, H.map_comp, Category.id_comp]
  erw [← Preadditive.comp_add, ← H.map_add_left, out_in_sum P,
    H.map_id, Category.comp_id]

private lemma bidualA_d {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    bidualA P I f p ≫ (hc F (hc F A I) I).d (p + 1) (p + 1 + 1) =
      -(hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).d p (p + 1) ≫
        bidualA P I f (p + 1) := by
  apply proj_ext P (hc F A I) I (p + 1 + 1)
  intro t
  erw [Category.assoc,
    d_proj P (hc F A I) I (p + 1) (p + 1 + 1) t (t + (p + 1 + 1))
      (t + (p + 1)) (t + 1) rfl rfl rfl (by omega),
    Preadditive.comp_sub, Linear.comp_units_smul, ← Category.assoc,
    bidualA_proj P, ← Category.assoc,
    bidualA_proj P I f p (t + 1) (t + (p + 1 + 1)) (by omega)]
  conv_rhs => erw [Preadditive.neg_comp, Category.assoc, bidualA_proj P,
    Linear.comp_units_smul, ← Category.assoc,
    d_proj P (hc F (HomologicalComplex.homotopyCofiber f) I) I p (p + 1)
      (t + 1) (t + (p + 1 + 1)) (t + (p + 1)) (t + 1 + 1)
      rfl (by omega) (by omega) (by omega)]
  simp only [Preadditive.sub_comp,  Linear.units_smul_comp,
    Category.assoc, H.map_comp,
    Category.id_comp, Category.comp_id, smul_sub,  smul_smul]
  erw [← inA_d P I f t]
  simp only [Int.negOnePow_add, Int.negOnePow_one,
    Units.neg_smul, neg_neg, sub_neg_eq_add,
     mul_neg, neg_neg,   mul_comm,
      mul_one]
  abel

private lemma bidualB_d {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).d p (p + 1) ≫
        bidualB P I f (p + 1) =
      bidualB P I f p ≫ (hc F (hc F B I) I).d p (p + 1) +
        bidualA P I f p ≫ ((doubleDualF F I).map f).f (p + 1) := by
  apply proj_ext P (hc F B I) I (p + 1)
  intro q
  erw [Category.assoc, bidualB_proj P, ← Category.assoc,
    d_proj P (hc F (HomologicalComplex.homotopyCofiber f) I) I p (p + 1)
      q (q + (p + 1)) (q + p) (q + 1) rfl rfl rfl (by omega)]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Linear.units_smul_comp,
    Category.assoc, H.map_comp,
     Category.comp_id]
  erw [inB_d P I f q, H.map_add_left, Preadditive.comp_add]
  conv_rhs => lhs; erw [d_proj P (hc F B I) I p (p + 1) q (q + (p + 1)) (q + p) (q + 1)
      rfl rfl rfl (by omega), Preadditive.comp_sub, Linear.comp_units_smul,
    ← Category.assoc, bidualB_proj P, ← Category.assoc, bidualB_proj P]
  conv_rhs => rhs; erw [
    dual_proj P I ((dualF F I).map f.op) (p + 1) q (q + (p + 1)) rfl,
    ← Category.assoc, bidualA_proj P]
  simp only [Linear.units_smul_comp, Category.assoc,
    H.map_comp, Category.id_comp, Category.comp_id,
      smul_add,
    Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, Units.neg_smul]
  simp only [ map_smul_left, Linear.comp_units_smul,
    smul_smul,  map_neg_left,
    Preadditive.comp_neg, smul_neg]
  abel

private noncomputable def thetaX {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).X p ⟶
      (CochainComplex.mappingCone ((doubleDualF F I).map f)).X p :=
  biprod.lift (bidualA P I f p) (bidualB P I f p) ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod ((doubleDualF F I).map f)
      p (p + 1) rfl).inv

private lemma thetaX_fst {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    thetaX P I f p ≫ HomologicalComplex.homotopyCofiber.fstX
      ((doubleDualF F I).map f) p (p + 1) rfl = bidualA P I f p := by
  simp [thetaX, HomologicalComplex.homotopyCofiber.fstX, Category.assoc]

private lemma thetaX_snd {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    thetaX P I f p ≫ HomologicalComplex.homotopyCofiber.sndX
      ((doubleDualF F I).map f) p = bidualB P I f p := by
  have he :
      (HomologicalComplex.homotopyCofiber.XIsoBiprod ((doubleDualF F I).map f)
        p (p + 1) rfl).inv ≫
          HomologicalComplex.homotopyCofiber.sndX ((doubleDualF F I).map f) p =
        biprod.snd := by
    apply biprod.hom_ext' <;> simp only [← Category.assoc,
      HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv,
      HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv,
      HomologicalComplex.homotopyCofiber.inlX_sndX,
      HomologicalComplex.homotopyCofiber.inrX_sndX, biprod.inl_snd, biprod.inr_snd]
  dsimp only [thetaX]
  erw [Category.assoc, he, biprod.lift_snd]

private noncomputable def thetaInvX {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (CochainComplex.mappingCone ((doubleDualF F I).map f)).X p ⟶
      (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).X p :=
  HomologicalComplex.homotopyCofiber.fstX ((doubleDualF F I).map f) p (p + 1) rfl ≫
      bidualInvA P I f p +
    HomologicalComplex.homotopyCofiber.sndX ((doubleDualF F I).map f) p ≫ bidualInvB P I f p

private lemma thetaX_inv {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    thetaX P I f p ≫ thetaInvX P I f p = 𝟙 _ := by
  dsimp only [thetaInvX]
  erw [Preadditive.comp_add, ← Category.assoc, thetaX_fst P,
    ← Category.assoc, thetaX_snd P, add_comm]
  exact bidual_sum P I f p

private lemma thetaInvX_hom {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    thetaInvX P I f p ≫ thetaX P I f p = 𝟙 _ := by
  apply HomologicalComplex.homotopyCofiber.ext_to_X ((doubleDualF F I).map f)
    p (p + 1) rfl
  · erw [Category.assoc, thetaX_fst P]
    simp only [thetaInvX, Preadditive.add_comp, Category.assoc,
      bidualInvA_A P, bidualInvB_A P, Category.comp_id, CategoryTheory.Limits.comp_zero,
      add_zero, Category.id_comp]
  · erw [Category.assoc, thetaX_snd P]
    simp only [thetaInvX, Preadditive.add_comp, Category.assoc,
      bidualInvA_B P, bidualInvB_B P, Category.comp_id, CategoryTheory.Limits.comp_zero,
      zero_add, Category.id_comp]

private noncomputable def thetaIsoX {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p : ℤ) :
    (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).X p ≅
      (CochainComplex.mappingCone ((doubleDualF F I).map f)).X p :=
  ⟨thetaX P I f p, thetaInvX P I f p, thetaX_inv P I f p, thetaInvX_hom P I f p⟩

-- Step 6: functoriality under commutative squares.
private lemma coneMap_fst {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b)
    (n : ℤ) :
    (coneMap h).f n ≫ HomologicalComplex.homotopyCofiber.fstX b.hom n (n + 1) rfl =
      HomologicalComplex.homotopyCofiber.fstX a.hom n (n + 1) rfl ≫ h.left.f (n + 1) := by
  apply HomologicalComplex.homotopyCofiber.ext_from_X a.hom (n + 1) n rfl
  · change (CochainComplex.mappingCone.inl a.hom).v (n + 1) n (by omega) ≫ _ = _
    simp only [coneMap, CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _ (n + 1) (n + 1) n
        (add_zero _) (show n + 1 + (-1) = n by omega),
      CochainComplex.HomComplex.Cochain.ofHom_v]
    simp [CochainComplex.mappingCone.inl]
  · change (CochainComplex.mappingCone.inr a.hom).f n ≫ _ = _
    simp only [coneMap, CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f]
    simp [CochainComplex.mappingCone.inr]

private lemma coneMap_snd {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b)
    (n : ℤ) :
    (coneMap h).f n ≫ HomologicalComplex.homotopyCofiber.sndX b.hom n =
      HomologicalComplex.homotopyCofiber.sndX a.hom n ≫ h.right.f n := by
  apply HomologicalComplex.homotopyCofiber.ext_from_X a.hom (n + 1) n rfl
  · change (CochainComplex.mappingCone.inl a.hom).v (n + 1) n (by omega) ≫ _ = _
    simp only [coneMap, CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _ (n + 1) (n + 1) n
        (add_zero _) (show n + 1 + (-1) = n by omega),
      CochainComplex.HomComplex.Cochain.ofHom_v]
    simp [CochainComplex.mappingCone.inl]
  · change (CochainComplex.mappingCone.inr a.hom).f n ≫ _ = _
    simp only [coneMap, CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f]
    simp [CochainComplex.mappingCone.inr]

private lemma inB_natural {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b) (q : ℤ) :
    ((dualF F I).map h.right.op).f q ≫ inB P I a.hom q =
      inB P I b.hom q ≫ ((dualF F I).map (coneMap h).op).f q := by
  dsimp only [CochainComplex.mappingCone, hc, dualF, doubleDualF] at *
  apply proj_ext P (CochainComplex.mappingCone a.hom) I q
  intro n
  erw [Category.assoc, inB_proj P, ← Category.assoc, dual_proj P,
    ]
  simp only [Category.assoc]
  erw [dual_proj P]
  conv_rhs => erw [← Category.assoc, inB_proj P]
  simp only [Category.assoc, H.map_comp, Category.id_comp]
  erw [coneMap_snd]

private lemma inA_natural {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b) (t : ℤ) :
    ((dualF F I).map h.left.op).f t ≫ inA P I a.hom t =
      inA P I b.hom t ≫ ((dualF F I).map (coneMap h).op).f (t + 1) := by
  dsimp only [CochainComplex.mappingCone, hc, dualF, doubleDualF] at *
  apply proj_ext P (CochainComplex.mappingCone a.hom) I (t + 1)
  intro n
  erw [Category.assoc, inA_proj P I a.hom t n (n + 1) _ rfl rfl,
    ← Category.assoc, dual_proj P,
    ]
  simp only [Category.assoc]
  erw [dual_proj P]
  conv_rhs => erw [← Category.assoc, inA_proj P I b.hom t n (n + 1) _ rfl rfl]
  simp only [Category.assoc, H.map_comp, Category.id_comp]
  erw [coneMap_fst]

private lemma bidualB_natural {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b) (p : ℤ) :
    ((doubleDualF F I).map (coneMap h)).f p ≫ bidualB P I b.hom p =
      bidualB P I a.hom p ≫ ((doubleDualF F I).map h.right).f p := by
  dsimp only [CochainComplex.mappingCone, hc, dualF, doubleDualF] at *
  apply proj_ext P (hc F b.right I) I p
  intro q
  erw [Category.assoc, bidualB_proj P, ← Category.assoc,
    dual_proj P I ((dualF F I).map (coneMap h).op),
    ]
  simp only [Category.assoc]
  erw [dual_proj P I ((dualF F I).map h.right.op)]
  conv_rhs => erw [← Category.assoc, bidualB_proj P]
  simp only [Category.assoc, H.map_comp, Category.id_comp]
  erw [inB_natural P]
  rfl

private lemma bidualA_natural {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b) (p : ℤ) :
    ((doubleDualF F I).map (coneMap h)).f p ≫ bidualA P I b.hom p =
      bidualA P I a.hom p ≫ ((doubleDualF F I).map h.left).f (p + 1) := by
  dsimp only [CochainComplex.mappingCone, hc, dualF, doubleDualF] at *
  apply proj_ext P (hc F b.left I) I (p + 1)
  intro t
  erw [Category.assoc, bidualA_proj P, Linear.comp_units_smul, ← Category.assoc,
    dual_proj P I ((dualF F I).map (coneMap h).op),
    ]
  simp only [Category.assoc]
  erw [dual_proj P I ((dualF F I).map h.left.op)]
  conv_rhs => erw [← Category.assoc, bidualA_proj P]
  simp only [Linear.units_smul_comp, Category.assoc,
    H.map_comp, Category.id_comp]
  erw [inA_natural P]
  rfl

private lemma theta_comm {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (p k : ℤ) (h : p + 1 = k) :
    thetaX P I f p ≫ (CochainComplex.mappingCone ((doubleDualF F I).map f)).d p k =
      (hc F (hc F (HomologicalComplex.homotopyCofiber f) I) I).d p k ≫ thetaX P I f k := by
  subst k
  dsimp only [CochainComplex.mappingCone]
  apply HomologicalComplex.homotopyCofiber.ext_to_X ((doubleDualF F I).map f)
    (p + 1) (p + 1 + 1) rfl
  · erw [Category.assoc]
    erw [HomologicalComplex.homotopyCofiber.d_fstX _ p (p + 1) (p + 1 + 1) rfl rfl,
      Preadditive.comp_neg, ← Category.assoc, thetaX_fst P,
      Category.assoc, thetaX_fst P, bidualA_d P]
    simp only [neg_neg]
  · erw [Category.assoc]
    erw [HomologicalComplex.homotopyCofiber.d_sndX _ p (p + 1) rfl,
      Preadditive.comp_add, ← Category.assoc, thetaX_fst P,
      ← Category.assoc, thetaX_snd P, Category.assoc, thetaX_snd P,
      bidualB_d P]
    exact add_comm _ _

private noncomputable def thetaIso {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) :
    (doubleDualF F I).obj (HomologicalComplex.homotopyCofiber f) ≅
      CochainComplex.mappingCone ((doubleDualF F I).map f) :=
  HomologicalComplex.Hom.isoOfComponents (thetaIsoX P I f) (theta_comm P I f)

private lemma theta_natural {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b) :
    (doubleDualF F I).map (coneMap h) ≫ (thetaIso P I b.hom).hom =
      (thetaIso P I a.hom).hom ≫ coneMap ((doubleDualF F I).mapArrow.map h) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.homotopyCofiber.ext_to_X ((doubleDualF F I).map b.hom)
    p (p + 1) rfl
  · change (((doubleDualF F I).map (coneMap h)).f p ≫ thetaX P I b.hom p) ≫ _ =
      (thetaX P I a.hom p ≫ (coneMap ((doubleDualF F I).mapArrow.map h)).f p) ≫ _
    erw [Category.assoc, thetaX_fst P, Category.assoc, coneMap_fst,
      ← Category.assoc, thetaX_fst P]
    exact bidualA_natural P I h p
  · change (((doubleDualF F I).map (coneMap h)).f p ≫ thetaX P I b.hom p) ≫ _ =
      (thetaX P I a.hom p ≫ (coneMap ((doubleDualF F I).mapArrow.map h)).f p) ≫ _
    erw [Category.assoc, thetaX_snd P, Category.assoc, coneMap_snd,
      ← Category.assoc, thetaX_snd P]
    exact bidualB_natural P I h p

private lemma theta_inr {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) :
    (doubleDualF F I).map (CochainComplex.mappingCone.inr f) ≫
        (thetaIso P I f).hom = CochainComplex.mappingCone.inr ((doubleDualF F I).map f) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.homotopyCofiber.ext_to_X ((doubleDualF F I).map f)
    p (p + 1) rfl
  · change (((doubleDualF F I).map (CochainComplex.mappingCone.inr f)).f p ≫
      thetaX P I f p) ≫ _ = _
    erw [Category.assoc, thetaX_fst P]
    apply proj_ext P (hc F A I) I (p + 1)
    intro t
    erw [Category.assoc, bidualA_proj P, Linear.comp_units_smul, ← Category.assoc,
      dual_proj P I ((dualF F I).map (CochainComplex.mappingCone.inr f).op)]
    simp only [CochainComplex.mappingCone.inr,
      HomologicalComplex.homotopyCofiber.inr_f,
      HomologicalComplex.homotopyCofiber.inrX_fstX, Limits.zero_comp]
    simp only [Category.assoc, H.map_comp,
      Category.id_comp]
    change _ • (_ ≫ H.map
      (inA P I f t ≫ outB P I f (t + 1)) (𝟙 _)) = _
    erw [inA_outB P, H.map_zero_left]
    simp
  · change (((doubleDualF F I).map (CochainComplex.mappingCone.inr f)).f p ≫
      thetaX P I f p) ≫ _ = _
    erw [Category.assoc, thetaX_snd P]
    apply proj_ext P (hc F B I) I p
    intro q
    erw [Category.assoc, bidualB_proj P, ← Category.assoc,
      dual_proj P I ((dualF F I).map (CochainComplex.mappingCone.inr f).op)]
    simp only [Category.assoc, H.map_comp,
      Category.id_comp]
    change _ ≫ H.map (inB P I f q ≫ outB P I f q) (𝟙 _) = _
    erw [inB_outB P, H.map_id, Category.comp_id]
    simp [CochainComplex.mappingCone.inr]

-- Steps 2 and 7: the composite shift comparison and the triangle arrows.
omit [HasBinaryBiproducts D] in
private lemma reindexOne_proj {H : HomData D} (P : Spec H F) (K I : CochainComplex D ℤ)
    (t a b : ℤ) (h : a + (t + 1) = b) :
    reindexOne P K I t ≫ P.π (K⟦(1 : ℤ)⟧) I (t + 1) a b h =
      P.π K I t (a + 1) b (by omega) := by
  subst b
  dsimp only [reindexOne]
  simpa only [ hc, fan_mk_proj, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, H.map_id, Category.comp_id] using
    (Fan.IsLimit.fac (productLimit P (K⟦(1 : ℤ)⟧) I (t + 1))
      (fun a : ℤ ↦ P.π K I t (a + 1) (a + (t + 1)) (by omega) ≫
        H.map (K.shiftFunctorObjXIso 1 a (a + 1) rfl).hom (𝟙 _)) a)

omit [HasBinaryBiproducts D] in
private lemma proj_degree {H : HomData D} (P : Spec H F)
    (K I : CochainComplex D ℤ) (n n' a b : ℤ) (hn : n = n')
    (h : a + n = b) (h' : a + n' = b) :
    ((hc F K I).XIsoOfEq hn).hom ≫ P.π K I n' a b h' = P.π K I n a b h := by
  subst n'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]

private lemma shift_inverse_one {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    (s : ∀ (K : CochainComplex D ℤ) (m : ℤ),
      hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧)
    (hs : ∀ (K : CochainComplex D ℤ) (m q a : ℤ),
      (s K m).hom.f q ≫ P.π K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • P.π (K⟦m⟧) I q a (a + q) rfl)
    (K : CochainComplex D ℤ) (t : ℤ) :
    (s K 1).inv.f (t + 1) =
      (t + 1).negOnePow •
        ((hc F K I).XIsoOfEq (show t + 1 + -1 = t by omega)).hom ≫
        reindexOne P K I t := by
  apply (cancel_epi ((s K 1).hom.f (t + 1))).mp
  apply proj_ext P (K⟦(1 : ℤ)⟧) I (t + 1)
  intro a
  have hid := congrArg (fun f ↦ f.f (t + 1)) (s K 1).hom_inv_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hid
  erw [hid, Category.id_comp]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc]
  erw [reindexOne_proj]
  have h := congrArg (fun z ↦ (t + 1).negOnePow • z) (hs K 1 (t + 1) a)
  simp only [one_mul, smul_smul, Int.units_mul_self, one_smul] at h
  symm
  convert! h using 1
  congr 1
  congr 1
  exact proj_degree P K I (t + 1 - 1) t (a + 1) (a + (t + 1))
    (by omega) (by omega) (by omega)

private noncomputable def chiIso {H : HomData D} (_P : Spec H F) (I : CochainComplex D ℤ)
    (s : ∀ (K : CochainComplex D ℤ) (m : ℤ),
      hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧)
    (K : CochainComplex D ℤ) :
    (doubleDualF F I).obj (K⟦(1 : ℤ)⟧) ≅ ((doubleDualF F I).obj K)⟦(1 : ℤ)⟧ :=
  -((dualF F I).mapIso (s K 1).symm.op ≪≫ s (hc F K I) (-1))

omit [HasBinaryBiproducts D] in
private lemma shift_proj_general {H : HomData D} (P : Spec H F)
    (I : CochainComplex D ℤ)
    (s : ∀ (K : CochainComplex D ℤ) (m : ℤ),
      hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧)
    (hs : ∀ (K : CochainComplex D ℤ) (m q a : ℤ),
      (s K m).hom.f q ≫ P.π K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • P.π (K⟦m⟧) I q a (a + q) rfl)
    (K : CochainComplex D ℤ) (m q a n c b : ℤ)
    (hn : q - m = n) (hc : a + m = c) (hb : a + q = b) :
    (s K m).hom.f q ≫ ((Calculation.hc F K I).XIsoOfEq hn).hom ≫
        P.π K I n c b (by omega) =
      (m * q).negOnePow • (P.π (K⟦m⟧) I q a b hb ≫
        H.map (K.XIsoOfEq hc).inv (𝟙 _)) := by
  subst n c b
  calc
    _ = (s K m).hom.f q ≫ P.π K I (q - m) (a + m) (a + q) (by omega) :=
      congrArg (fun z ↦ (s K m).hom.f q ≫ z)
        (Category.id_comp (P.π K I (q - m) (a + m) (a + q) (by omega)))
    _ = _ := hs K m q a
    _ = _ := congrArg (fun z ↦ (m * q).negOnePow • z)
      ((congrArg (fun z ↦ P.π (K⟦m⟧) I q a (a + q) rfl ≫ z)
        (H.map_id (K.X (a + m)) (I.X (a + q)))).trans (Category.comp_id _)).symm

private lemma chi_proj {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    (s : ∀ (K : CochainComplex D ℤ) (m : ℤ),
      hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧)
    (hs : ∀ (K : CochainComplex D ℤ) (m q a : ℤ),
      (s K m).hom.f q ≫ P.π K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • P.π (K⟦m⟧) I q a (a + q) rfl)
    (K : CochainComplex D ℤ) (p t : ℤ) :
    (chiIso P I s K).hom.f p ≫ P.π (hc F K I) I (p + 1) t (t + (p + 1)) rfl =
      (p + t).negOnePow •
        (P.π (hc F (K⟦(1 : ℤ)⟧) I) I p (t + 1) (t + (p + 1)) (by omega) ≫
          H.map (reindexOne P K I t) (𝟙 _)) := by
  dsimp only [chiIso, Preadditive.neg_iso_hom, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Iso.symm_inv, HomologicalComplex.neg_f_apply, HomologicalComplex.comp_f]
  have h := shift_proj_general P I s hs (hc F K I) (-1) p (t + 1)
    (p + 1) t (t + (p + 1)) (by omega) (by omega) (by omega)
  simp only [Int.reduceNeg, neg_one_mul,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom] at h
  have hid := Category.id_comp (P.π (hc F K I) I (p + 1) t (t + (p + 1)) rfl)
  erw [hid] at h
  erw [Preadditive.neg_comp, Category.assoc, h,
    Linear.comp_units_smul, ← Category.assoc, dual_proj P]
  erw [shift_inverse_one P I s hs]
  simp only [Category.assoc, H.map_comp, Category.id_comp,
    Linear.units_smul_comp, map_smul_left, Linear.comp_units_smul, smul_smul]
  have hi := Iso.inv_hom_id_assoc
    ((hc F K I).XIsoOfEq (show t + 1 + -1 = t by omega)) (reindexOne P K I t)
  erw [hi]
  simp only [Int.negOnePow_neg, Int.negOnePow_add, Int.negOnePow_one,
    mul_neg, Units.neg_smul, neg_neg, mul_one]

private lemma triangle_f {A B : CochainComplex D ℤ} (f : A ⟶ B) (n : ℤ) :
    (CochainComplex.mappingCone.triangle f).mor₃.f n =
      -HomologicalComplex.homotopyCofiber.fstX f n (n + 1) rfl := by
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n + 1) n rfl
  · change (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫ _ = _
    simp
  · change (CochainComplex.mappingCone.inr f).f n ≫ _ = _
    erw [CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
    simp only [Preadditive.comp_neg,
      HomologicalComplex.homotopyCofiber.inrX_fstX, neg_zero]

private lemma reindex_triangle {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) (t : ℤ) :
    reindexOne P A I t ≫
        ((dualF F I).map (CochainComplex.mappingCone.triangle f).mor₃.op).f (t + 1) =
      -inA P I f t := by
  apply proj_ext P (CochainComplex.mappingCone f) I (t + 1)
  intro a
  simp only [Category.assoc]
  erw [dual_proj P]
  conv_lhs => erw [← Category.assoc, reindexOne_proj P]
  simp only [Preadditive.neg_comp]
  erw [inA_proj P I f t a (a + 1) _ rfl rfl, triangle_f, map_neg_left,
    Preadditive.comp_neg]

private lemma theta_triangle {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ)
    (s : ∀ (K : CochainComplex D ℤ) (m : ℤ),
      hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧)
    (hs : ∀ (K : CochainComplex D ℤ) (m q a : ℤ),
      (s K m).hom.f q ≫ P.π K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • P.π (K⟦m⟧) I q a (a + q) rfl)
    {A B : CochainComplex D ℤ} (f : A ⟶ B) :
    (doubleDualF F I).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (chiIso P I s A).hom =
      (thetaIso P I f).hom ≫
        (CochainComplex.mappingCone.triangle ((doubleDualF F I).map f)).mor₃ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply proj_ext P (hc F A I) I (p + 1)
  intro t
  change ((((doubleDualF F I).map (CochainComplex.mappingCone.triangle f).mor₃).f p ≫
    (chiIso P I s A).hom.f p) ≫ _) = (thetaX P I f p ≫ _) ≫ _
  erw [Category.assoc, chi_proj P I s hs, Linear.comp_units_smul, ← Category.assoc,
    dual_proj P I ((dualF F I).map (CochainComplex.mappingCone.triangle f).mor₃.op),
    triangle_f, Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc,
    thetaX_fst P, bidualA_proj P]
  simp only [H.map_comp, Category.id_comp]
  erw [reindex_triangle P, map_neg_left, Preadditive.comp_neg, smul_neg]
  rfl

private theorem result {H : HomData D} (P : Spec H F) (I : CochainComplex D ℤ) :
    ∃ s : ∀ (K : CochainComplex D ℤ) (m : ℤ),
      hc F (K⟦m⟧) I ≅ (hc F K I)⟦-m⟧,
    ∃ chi : ∀ K : CochainComplex D ℤ,
      (doubleDualF F I).obj (K⟦(1 : ℤ)⟧) ≅ ((doubleDualF F I).obj K)⟦(1 : ℤ)⟧,
    ∃ theta : ∀ {A B : CochainComplex D ℤ} (f : A ⟶ B),
      (doubleDualF F I).obj (CochainComplex.mappingCone f) ≅
        CochainComplex.mappingCone ((doubleDualF F I).map f),
    (∀ (K : CochainComplex D ℤ) (m q a : ℤ),
      (s K m).hom.f q ≫
          ((hc F K I).shiftFunctorObjXIso (-m) q (q - m) (by omega)).hom ≫
          P.π K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • (P.π (K⟦m⟧) I q a (a + q) rfl ≫
          H.map (K.shiftFunctorObjXIso m a (a + m) rfl).inv (𝟙 _))) ∧
    (∀ {K L : CochainComplex D ℤ} (f : K ⟶ L) (m : ℤ),
      (dualF F I).map (f⟦m⟧').op ≫ (s K m).hom =
        (s L m).hom ≫ ((dualF F I).map f.op)⟦-m⟧') ∧
    (∀ K : CochainComplex D ℤ,
      (chi K).hom = -((dualF F I).map (s K 1).inv.op ≫ (s (hc F K I) (-1)).hom)) ∧
    (∀ (K : CochainComplex D ℤ) (p t : ℤ),
      (chi K).hom.f p ≫
          (((doubleDualF F I).obj K).shiftFunctorObjXIso 1 p (p + 1) rfl).hom ≫
          P.π (hc F K I) I (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (P.π (hc F (K⟦(1 : ℤ)⟧) I) I p (t + 1) (t + (p + 1)) (by omega) ≫
            H.map (reindexOne P K I t) (𝟙 _))) ∧
    (∀ {A B : CochainComplex D ℤ} (f : A ⟶ B) (p q : ℤ),
      (theta f).hom.f p ≫
          HomologicalComplex.homotopyCofiber.sndX ((doubleDualF F I).map f) p ≫
          P.π (hc F B I) I p q (q + p) rfl =
        P.π (hc F (CochainComplex.mappingCone f) I) I p q (q + p) rfl ≫
          H.map (inB P I f q) (𝟙 _)) ∧
    (∀ {A B : CochainComplex D ℤ} (f : A ⟶ B) (p t : ℤ),
      (theta f).hom.f p ≫
          HomologicalComplex.homotopyCofiber.fstX ((doubleDualF F I).map f) p (p + 1) rfl ≫
          P.π (hc F A I) I (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (P.π (hc F (CochainComplex.mappingCone f) I) I p (t + 1)
            (t + (p + 1)) (by omega) ≫ H.map (inA P I f t) (𝟙 _))) ∧
    (∀ {a b : Arrow (CochainComplex D ℤ)} (h : a ⟶ b),
      (doubleDualF F I).map (coneMap h) ≫ (theta b.hom).hom =
        (theta a.hom).hom ≫ coneMap ((doubleDualF F I).mapArrow.map h)) ∧
    (∀ {A B : CochainComplex D ℤ} (f : A ⟶ B),
      (doubleDualF F I).map (CochainComplex.mappingCone.inr f) ≫ (theta f).hom =
        CochainComplex.mappingCone.inr ((doubleDualF F I).map f)) ∧
    (∀ {A B : CochainComplex D ℤ} (f : A ⟶ B),
      (doubleDualF F I).map (CochainComplex.mappingCone.triangle f).mor₃ ≫ (chi A).hom =
        (theta f).hom ≫ (CochainComplex.mappingCone.triangle ((doubleDualF F I).map f)).mor₃) := by
  classical
  let s (K : CochainComplex D ℤ) (m : ℤ) :=
    Classical.choose (shift_exists P I K m)
  have hs := fun K m ↦ Classical.choose_spec (shift_exists P I K m)
  have hs' (K : CochainComplex D ℤ) (m q a : ℤ) :
      (s K m).hom.f q ≫ P.π K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • P.π (K⟦m⟧) I q a (a + q) rfl := by
    simpa only [reindexOne, hc, fan_mk_proj, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp, Category.comp_id, H.map_id, CochainComplex.shiftFunctor_obj_X',
      CochainComplex.shiftFunctor_obj_X, s] using hs K m q a
  refine ⟨s, chiIso P I s, fun f ↦ thetaIso P I f, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun f m ↦ shift_natural P I s hs' f m
  · intro K
    rfl
  · intro K p t
    simpa only [reindexOne, hc, fan_mk_proj, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
      CochainComplex.shiftFunctor_obj_X',
      CochainComplex.shiftFunctor_obj_X] using
      chi_proj P I s hs' K p t
  · intro A B f p q
    dsimp only [thetaIso, HomologicalComplex.Hom.isoOfComponents_hom_f, thetaIsoX]
    erw [← Category.assoc]
    erw [thetaX_snd P, bidualB_proj P]
    rfl
  · intro A B f p t
    dsimp only [thetaIso, HomologicalComplex.Hom.isoOfComponents_hom_f, thetaIsoX]
    erw [← Category.assoc]
    erw [thetaX_fst P, bidualA_proj P]
    rfl
  · exact fun h ↦ theta_natural P I h
  · exact fun f ↦ theta_inr P I f
  · exact fun f ↦ theta_triangle P I s hs' f

end Calculation

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}

/-- Internal Hom into the fixed complex, using the recorded Hom bifunctor.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable abbrev dual (I : Complex.{u, v, w, r} R) :
    (Complex.{u, v, w, r} R)ᵒᵖ ⥤ Complex.{u, v, w, r} R :=
  (homComplexFunctor (R := R)).flip.obj I

/-- Twice applying the same contravariant internal Hom.
Source: Stacks 08JC (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable abbrev doubleDual (I : Complex.{u, v, w, r} R) :
    Complex.{u, v, w, r} R ⥤ Complex.{u, v, w, r} R :=
  (dual I).rightOp ⋙ dual I

/-- Reindex T(K)^t into T(K[1])^(t+1) without multiplying by a sign.
Source: Stacks 0A8X (blueprint: lem-sf-double-hom-cone-comparison). -/
noncomputable def reindexOne (K I : Complex.{u, v, w, r} R) (t : ℤ) :
    (homComplex K I).X t ⟶ (homComplex (K⟦(1 : ℤ)⟧) I).X (t + 1) :=
  Fan.IsLimit.lift (productLimit _ I (t + 1)) (fun a : ℤ ↦
    proj K I t (a + 1) (a + (t + 1)) (by omega) ≫
      SheafOfModules.homObjMap (K.shiftFunctorObjXIso 1 a (a + 1) rfl).hom (𝟙 _))

private lemma map_add_left {A A' B B' : Modules.{u, v, w, r} R}
    (f g : A' ⟶ A) (h : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (f + g) h =
      SheafOfModules.homObjMap f h + SheafOfModules.homObjMap g h :=
  SheafOfModules.hom_ext (PresheafOfModules.homObjMap_add_left f.val g.val h.val)

private lemma map_zero_left {A A' B B' : Modules.{u, v, w, r} R} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) g = 0 :=
  SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left g.val)

/-- Signed shift and cone comparisons for double internal Hom into an arbitrary I.
Source: Stacks 014E and 0A8X; explicit calculation filling the omission in 08JC
(blueprint: lem-sf-double-hom-cone-comparison).

Proof: (1) Write eps(t)=(-1)^t. Reindexing a degree q map from K[m] gives degree
q-m from K. Multiplication by eps(mq) intertwines the two differentials: both
sides are eps(mq+m)d_I f - eps(mq+q)f d_K. The same sign gives the inverse;
precomposition proves naturality. (2) Define chi as minus s at (T(K),-1)
after T(s at (K,1)) inverse. On y of degree t its sign is
-eps(p)eps(t+1)=eps(p+t). (3) Restricting maps from the binary cone summands
gives T(E)^q=X^q plus Y^(q-1); its differential is
(d_X x, d_Y y + eps(q+1)T(u)x). (4) Applying Hom again gives
alpha'_q=d_I alpha_q-eps(p)alpha_(q+1)d_X+eps(p+q)beta_q T(u),
and beta'_t=d_I beta_t-eps(p)beta_(t+1)d_Y. (5) Set gamma_t=eps(p+t)beta_t.
Then the differential is (d alpha+T²(u)gamma,-d gamma), the cone differential.
The same sign constructs the inverse. (6) For a square, cone maps act diagonally
on X and Y, and these actions commute with eps(p+t), proving naturality.
(7) T²(i) sends alpha to (alpha,0). T²(-pi) evaluates to -beta, and chi
turns this into -gamma, which is -pi after theta. These are equations of
restricted module maps, so they hold as sheaf maps. Only binary sums, products,
reindexing and signs are used; there is no boundedness, flatness or K-injectivity.
-/
theorem comparison (I : Complex.{u, v, w, r} R) :
    ∃ s : ∀ (K : Complex.{u, v, w, r} R) (m : ℤ),
      homComplex (K⟦m⟧) I ≅ (homComplex K I)⟦-m⟧,
    ∃ chi : ∀ K : Complex.{u, v, w, r} R,
      (doubleDual I).obj (K⟦(1 : ℤ)⟧) ≅ ((doubleDual I).obj K)⟦(1 : ℤ)⟧,
    ∃ theta : ∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B),
      (doubleDual I).obj (CochainComplex.mappingCone f) ≅
        CochainComplex.mappingCone ((doubleDual I).map f),
    (∀ (K : Complex.{u, v, w, r} R) (m q a : ℤ),
      (s K m).hom.f q ≫
          ((homComplex K I).shiftFunctorObjXIso (-m) q (q - m) (by omega)).hom ≫
          proj K I (q - m) (a + m) (a + q) (by omega) =
        (m * q).negOnePow • (proj (K⟦m⟧) I q a (a + q) rfl ≫
          SheafOfModules.homObjMap (K.shiftFunctorObjXIso m a (a + m) rfl).inv (𝟙 _))) ∧
    (∀ {K L : Complex.{u, v, w, r} R} (f : K ⟶ L) (m : ℤ),
      (dual I).map (f⟦m⟧').op ≫ (s K m).hom =
        (s L m).hom ≫ ((dual I).map f.op)⟦-m⟧') ∧
    (∀ K : Complex.{u, v, w, r} R,
      (chi K).hom = -((dual I).map (s K 1).inv.op ≫ (s (homComplex K I) (-1)).hom)) ∧
    (∀ (K : Complex.{u, v, w, r} R) (p t : ℤ),
      (chi K).hom.f p ≫
          (((doubleDual I).obj K).shiftFunctorObjXIso 1 p (p + 1) rfl).hom ≫
          proj (homComplex K I) I (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (proj (homComplex (K⟦(1 : ℤ)⟧) I) I p (t + 1) (t + (p + 1)) (by omega) ≫
            SheafOfModules.homObjMap (reindexOne K I t) (𝟙 _))) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (p q : ℤ),
      (theta f).hom.f p ≫
          HomologicalComplex.homotopyCofiber.sndX ((doubleDual I).map f) p ≫
          proj (homComplex B I) I p q (q + p) rfl =
        proj (homComplex (CochainComplex.mappingCone f) I) I p q (q + p) rfl ≫
          SheafOfModules.homObjMap (inB I f q) (𝟙 _)) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (p t : ℤ),
      (theta f).hom.f p ≫
          HomologicalComplex.homotopyCofiber.fstX ((doubleDual I).map f) p (p + 1) rfl ≫
          proj (homComplex A I) I (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (proj (homComplex (CochainComplex.mappingCone f) I) I p (t + 1)
            (t + (p + 1)) (by omega) ≫ SheafOfModules.homObjMap (inA I f t) (𝟙 _))) ∧
    (∀ {a b : Arrow (Complex.{u, v, w, r} R)} (h : a ⟶ b),
      (doubleDual I).map (coneMap h) ≫ (theta b.hom).hom =
        (theta a.hom).hom ≫ coneMap ((doubleDual I).mapArrow.map h)) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B),
      (doubleDual I).map (CochainComplex.mappingCone.inr f) ≫ (theta f).hom =
        CochainComplex.mappingCone.inr ((doubleDual I).map f)) ∧
    (∀ {A B : Complex.{u, v, w, r} R} (f : A ⟶ B),
      (doubleDual I).map (CochainComplex.mappingCone.triangle f).mor₃ ≫ (chi A).hom =
        (theta f).hom ≫ (CochainComplex.mappingCone.triangle ((doubleDual I).map f)).mor₃) := by
  let H : Calculation.HomData (Modules.{u, v, w, r} R) :=
    { obj := SheafOfModules.homObj
      map := fun f g ↦ SheafOfModules.homObjMap f g
      map_id := fun _ _ ↦ SheafOfModules.homObjMap_id
      map_comp := fun f f' g g' ↦ SheafOfModules.homObjMap_comp_homObjMap f f' g g'
      map_add_left := map_add_left
      map_zero_left := map_zero_left }
  let P : Calculation.Spec H (homComplexFunctor (R := R)) :=
    { π := proj
      lim := productLimit
      diff := homComplex_d_π
      map := fun _ _ _ _ f g n a b h ↦ homComplexFunctor_map_f_π f g n a b h }
  exact Calculation.result P I

end CategoryTheory.SignedDoubleHomCone
