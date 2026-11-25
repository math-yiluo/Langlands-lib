/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-!
# Signed double internal Hom and mapping cones

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08JC;
derived.tex, Definition 014E (auxiliary; not a blueprint node).
The component equations below are equations of module sheaves, hence include every
local section and all restriction maps. Mathlib orders the cone summands as A[1], B.
-/

@[expose] public section


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
end Calculation

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}

/-- The module category used in the signed comparison; this is just the recorded
ringed-site module category, in a universe containing the small site.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{max u v w, r, v, u}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Integer cochain complexes in the recorded module category.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
abbrev Complex (R : Sheaf J CommRingCat.{r}) := CochainComplex (Modules.{u, v, w, r} R) ℤ

/-- Binary biproducts computed from the existing sectionwise products. This supplies
cones without any sheafification or injectivity assumption.
Source: Stacks 014E (auxiliary; not a blueprint node). -/
noncomputable instance moduleBinaryBiproducts : HasBinaryBiproducts (Modules.{u, v, w, r} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The specified product projection of the existing Hom complex, with an explicit
index equality for reindexing.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
noncomputable def proj (K I : Complex.{u, v, w, r} R) (n a b : ℤ) (h : a + n = b) :
    (homComplex K I).X n ⟶ SheafOfModules.homObj (K.X a) (I.X b) :=
  homComplexπ K I n a b h

/-- The existing product universal property, with the same projections as `proj`.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
noncomputable def productLimit (K I : Complex.{u, v, w, r} R) (n : ℤ) :
    IsLimit (Fan.mk ((homComplex K I).X n) (fun a : ℤ ↦ proj K I n a (a + n) rfl)) :=
  homComplexIsLimit K I n

/-- The unsigned graded inclusion X^q into T(Cone u)^q, extending maps by zero
on the A[1] summand. Its data come from the product universal property.
Source: Stacks 014E and 0A8X (auxiliary; not a blueprint node). -/
noncomputable def inB (I : Complex.{u, v, w, r} R)
    {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (q : ℤ) :
    (homComplex B I).X q ⟶ (homComplex (CochainComplex.mappingCone f) I).X q :=
  Fan.IsLimit.lift (productLimit _ I q) (fun a : ℤ ↦
    proj B I q a (a + q) rfl ≫
      SheafOfModules.homObjMap (HomologicalComplex.homotopyCofiber.sndX f a) (𝟙 _))

/-- The unsigned graded inclusion Y^r into T(Cone u)^(r+1), extending maps by
zero on the B summand.
Source: Stacks 014E and 0A8X (auxiliary; not a blueprint node). -/
noncomputable def inA (I : Complex.{u, v, w, r} R)
    {A B : Complex.{u, v, w, r} R} (f : A ⟶ B) (t : ℤ) :
    (homComplex A I).X t ⟶ (homComplex (CochainComplex.mappingCone f) I).X (t + 1) :=
  Fan.IsLimit.lift (productLimit _ I (t + 1)) (fun a : ℤ ↦
    proj A I t (a + 1) (a + (t + 1)) (by omega) ≫
      SheafOfModules.homObjMap
        (HomologicalComplex.homotopyCofiber.fstX f a (a + 1) rfl) (𝟙 _))

/-- The cone map induced by a commutative square, with no homotopy correction.
Source: Stacks 014E (auxiliary; not a blueprint node). -/
noncomputable abbrev coneMap {a b : Arrow (Complex.{u, v, w, r} R)} (h : a ⟶ b) :=
  CochainComplex.mappingCone.map a.hom b.hom h.left h.right h.w.symm

private lemma map_add_left {A A' B B' : Modules.{u, v, w, r} R}
    (f g : A' ⟶ A) (h : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (f + g) h =
      SheafOfModules.homObjMap f h + SheafOfModules.homObjMap g h :=
  SheafOfModules.hom_ext (PresheafOfModules.homObjMap_add_left f.val g.val h.val)

private lemma map_zero_left {A A' B B' : Modules.{u, v, w, r} R} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) g = 0 :=
  SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left g.val)

end CategoryTheory.SignedDoubleHomCone
