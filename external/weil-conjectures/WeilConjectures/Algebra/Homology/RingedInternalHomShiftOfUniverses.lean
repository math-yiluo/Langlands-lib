/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModel
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses

/-! # Normalized internal-Hom shifts with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 0A8X, 08JA and 08JC
(auxiliary; not a blueprint node).
The existing restriction and signed small-site interfaces are reexported. The
normalizations below use the very same Hom complex, its fixed product projections,
and its fixed augmentation to the K-injective localization.

The private arguments first establish reindexing and cone comparisons for an
abstract product Hom complex. They then descend natural transformations through
localization, specialize the fixed sheaf Hom data, and prove normalization and
uniqueness. Keeping this algebra abstract avoids unfolding the concrete sheaf
Hom construction in every chain and triangle identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The recorded modules, retaining both site universes.
Source: Stacks 08J7 (auxiliary; not a blueprint node). -/
abbrev Modules := SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- The recorded cochain category.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
abbrev Complex := CochainComplex (Modules.{c, v, r} J R) ℤ

/-- The recorded Hom complex, without a second construction.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
abbrev complexHom (L F : Complex.{c, v, r} J R) :=
  homComplex.{c, v, max c v r, max c v r} (R := R) L F

/-- Unsigned target reindexing, specified on every Hom-product projection.
Source: Stacks 0A8X (auxiliary; not a blueprint node). -/
def RightFormula (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e : (complexHom.{c, v, r} J R L F)⟦s⟧ ≅ complexHom.{c, v, r} J R L (F⟦s⟧)) : Prop :=
  ∀ (k p q : ℤ) (h : p + k = q),
    e.hom.f k ≫ homComplexπ.{c, v, max c v r, max c v r} (R := R) L (F⟦s⟧) k p q h =
      homComplexπ.{c, v, max c v r, max c v r} (R := R) L F (k + s) p (q + s)
        (by omega)

/-- Signed source reindexing: in Hom degree k multiply the reindexed family
by (-1)^(s*k). Source: Stacks 0A8X
(auxiliary; not a blueprint node). -/
def LeftFormula (L F : Complex.{c, v, r} J R) (s : ℤ)
    (e : (complexHom.{c, v, r} J R L F)⟦-s⟧ ≅ complexHom.{c, v, r} J R (L⟦s⟧) F) : Prop :=
  ∀ (k p q : ℤ) (h : p + k = q),
    e.hom.f k ≫ homComplexπ.{c, v, max c v r, max c v r} (R := R) (L⟦s⟧) F k p q h =
      (s * k).negOnePow •
        (homComplexπ.{c, v, max c v r, max c v r} (R := R) L F (k + -s) (p + s) q
          (by omega))

set_option backward.isDefEq.respectTransparency true in
private lemma homObjMap_neg_left
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (-f) g =
      -SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f g := by
  apply SheafOfModules.hom_ext.{max c v r, v, c, max c v r}
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map (-f.val) ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map g.val =
    -((PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map g.val)
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (-((f.val.app _).hom x))) =
    -((g.val.app _).hom) ((φ.app W).hom ((f.val.app _).hom x))
  erw [map_neg, map_neg]

set_option backward.isDefEq.respectTransparency true in
private lemma homObjMap_units_smul_left
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (r : ℤˣ) (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (r • f) g =
      r • SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f g := by
  rcases Int.units_eq_one_or r with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul]
    exact homObjMap_neg_left.{c, v, r} f g

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem ordinaryLeftShiftAux
    {A : Type*} [Category A] [Preadditive A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hsmul : ∀ {X X' Y Y' : A} (a : ℤˣ) (f : X' ⟶ X) (g : Y ⟶ Y'),
      Hmap (a • f) g = a • Hmap f g)
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (L : CochainComplex A ℤ) (m : ℤ) :
    ∃ iso : ((F.obj (op L)) ⋙ shiftFunctor _ (-m)) ≅ F.obj (op (L⟦m⟧)),
      ∀ (M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q),
        (iso.app M).hom.f k ≫ π (L⟦m⟧) M k p q h =
          (m * k).negOnePow • (π L M (k + -m) (p + m) q (by omega) ≫
            Hmap
              (L.shiftFunctorObjXIso m p (p + m) rfl).hom (𝟙 (M.X q))) := by
  classical
  have hp (L M : CochainComplex A ℤ) (n : ℤ) := Classical.choice (hπ₁ L M n)
  let S := L⟦m⟧
  let K (M : CochainComplex A ℤ) := ((F.obj (op L)).obj M)⟦-m⟧
  let T (M : CochainComplex A ℤ) := (F.obj (op S)).obj M
  let a (M : CochainComplex A ℤ) (n : ℤ) : (K M).X n ⟶ (T M).X n :=
    Fan.IsLimit.lift (hp S M n) (fun p ↦
      (m * n).negOnePow • π L M (n - m) (p + m) (p + n) (by omega))
  have ha (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q) :
      a M n ≫ π S M n p q h =
        (m * n).negOnePow • π L M (n - m) (p + m) q (by omega) := by
    subst q
    exact Fan.IsLimit.fac (hp S M n) _ p
  let b (M : CochainComplex A ℤ) (n : ℤ) : (T M).X n ⟶ (K M).X n :=
    Fan.IsLimit.lift (hp L M (n - m)) (fun p ↦
      (m * n).negOnePow • (π S M n (p - m) (p + (n - m)) (by omega) ≫
        Hmap
          (L.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)))
  have hb (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + (n - m) = q) :
      b M n ≫ π L M (n - m) p q h =
        (m * n).negOnePow • (π S M n (p - m) q (by omega) ≫
          Hmap
            (L.XIsoOfEq (show p - m + m = p by omega)).inv (𝟙 _)) := by
    subst q
    exact Fan.IsLimit.fac (hp L M (n - m)) _ p
  have hπeq (Lc M : CochainComplex A ℤ) (n p p' q : ℤ)
      (h : p' = p) (hq : p + n = q) :
      π Lc M n p' q (by omega) ≫
          Hmap (Lc.XIsoOfEq h).inv (𝟙 _) = π Lc M n p q hq := by
    subst p'
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      hid, Category.comp_id]
  have hab (M : CochainComplex A ℤ) (n : ℤ) : a M n ≫ b M n = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext (hp L M (n - m))
    intro p
    change (a M n ≫ b M n) ≫ π L M (n - m) p (p + (n - m)) rfl = _
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    rw [Category.assoc, hb, Linear.comp_units_smul, ← Category.assoc, ha]
    simp only [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul, Category.id_comp]
    change _ = π L M (n - m) p (p + (n - m)) rfl
    exact hπeq L M (n - m) p (p - m + m) (p + (n - m)) (by omega) rfl
  have hba (M : CochainComplex A ℤ) (n : ℤ) : b M n ≫ a M n = 𝟙 _ := by
    apply Fan.IsLimit.hom_ext (hp S M n)
    intro p
    change (b M n ≫ a M n) ≫ π S M n p (p + n) rfl = _
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a b ha hb ⊢
    rw [Category.assoc, ha, Linear.comp_units_smul, hb]
    simp only [smul_smul, Int.units_mul_self, one_smul, Category.id_comp]
    change _ = π S M n p (p + n) rfl
    exact hπeq S M n p (p + m - m) (p + n) (by omega) rfl
  let e (M : CochainComplex A ℤ) (n : ℤ) : (K M).X n ≅ (T M).X n :=
    ⟨a M n, b M n, hab M n, hba M n⟩
  have hm (Lc M N : CochainComplex A ℤ) (f : M ⟶ N)
      (n p q : ℤ) (h : p + n = q) :
      ((F.obj (op Lc)).map f).f n ≫ π Lc N n p q h =
        π Lc M n p q h ≫ Hmap (𝟙 (Lc.X p)) (f.f q) := by
    simpa only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
      HomologicalComplex.id_f] using hπ₃ Lc Lc M N (𝟙 Lc) f n p q h
  have hc (M : CochainComplex A ℤ) (n k : ℤ) (h : n + 1 = k) :
      (e M n).hom ≫ (T M).d n k = (K M).d n k ≫ (e M k).hom := by
    subst k
    dsimp only [K, CochainComplex.shiftFunctor_obj_X'] at a ha ⊢
    apply Fan.IsLimit.hom_ext (hp S M (n + 1))
    intro p
    change (a M n ≫ (T M).d n (n + 1)) ≫ π S M (n + 1) p (p + (n + 1)) rfl =
      (((-m).negOnePow • ((F.obj (op L)).obj M).d (n - m) (n + 1 - m)) ≫
        a M (n + 1)) ≫ π S M (n + 1) p (p + (n + 1)) rfl
    rw [Category.assoc,
      hπ₂ S M n (n + 1) p (p + (n + 1)) (p + n) (p + 1)
        rfl rfl rfl (by omega),
      Preadditive.comp_sub, Linear.comp_units_smul, ← Category.assoc,
      ha M n p (p + n) rfl, ← Category.assoc,
      ha M n (p + 1) (p + (n + 1)) (by omega), Category.assoc]
    conv_rhs => rw [ha M (n + 1) p (p + (n + 1)) rfl]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul]
    rw [hπ₂ L M (n - m) (n + 1 - m) (p + m) (p + (n + 1)) (p + n) (p + 1 + m)
        (by omega) (by omega) (by omega) (by omega)]
    simp only [S, CochainComplex.shiftFunctor_obj_d']
    dsimp only [CochainComplex.shiftFunctor_obj_X']
    conv_lhs =>
      rhs
      arg 2
      rhs
      rw [hsmul m.negOnePow
        (L.d (p + m) (p + 1 + m)) (𝟙 (M.X (p + (n + 1))))]
    simp only [Linear.comp_units_smul, smul_sub, smul_smul,
      Int.negOnePow_neg, Int.negOnePow_sub]
    have hs : (m * (n + 1)).negOnePow = (m * n).negOnePow * m.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    simp only [hs, mul_assoc, Int.units_mul_self, mul_one]
    rw [mul_left_comm n.negOnePow (m * n).negOnePow m.negOnePow]
  let iso : ((F).obj (op L) ⋙ shiftFunctor _ (-m)) ≅
      (F).obj (op (L⟦m⟧)) :=
    NatIso.ofComponents (fun M ↦
    HomologicalComplex.Hom.isoOfComponents (e M) (hc M)) (by
    intro M N f
    apply HomologicalComplex.hom_ext
    intro n
    change ((F.obj (op L)).map f).f (n - m) ≫ a N n =
      a M n ≫ ((F.obj (op S)).map f).f n
    apply Fan.IsLimit.hom_ext (hp S N n)
    intro p
    change (((F.obj (op L)).map f).f (n - m) ≫ a N n) ≫
        π S N n p (p + n) rfl =
      (a M n ≫ ((F.obj (op S)).map f).f n) ≫ π S N n p (p + n) rfl
    rw [Category.assoc, ha, Linear.comp_units_smul, hm, Category.assoc, hm,
      ← Category.assoc, ha, Linear.units_smul_comp]
    rfl)
  refine ⟨iso, ?_⟩
  intro M k p q h
  change (a M k) ≫ π S M k p q h = _
  simp only [CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    hid,
    Category.comp_id]
  exact ha M k p q h

private theorem ordinaryLeftShiftBifunctorAux
    {A : Type*} [Category A] [Preadditive A]
    (Hobj : A → A → A)
    (Hmap : ∀ {X X' Y Y' : A}, (X' ⟶ X) → (Y ⟶ Y') →
      (Hobj X Y ⟶ Hobj X' Y'))
    (hid : ∀ X Y : A, Hmap (𝟙 X) (𝟙 Y) = 𝟙 (Hobj X Y))
    (hsmul : ∀ {X X' Y Y' : A} (a : ℤˣ) (f : X' ⟶ X) (g : Y ⟶ Y'),
      Hmap (a • f) g = a • Hmap f g)
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ), p + n = q →
      (((F.obj (op L)).obj M).X n ⟶ Hobj (L.X p) (M.X q)))
    (hπ₁ : ∀ (L M : CochainComplex A ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
        (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hπ₂ : ∀ (L M : CochainComplex A ℤ) (n k p q q' p' : ℤ),
      n + 1 = k → ∀ (hpq : p + k = q) (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj M).d n k ≫ π L M k p q hpq =
        π L M n p q' hq' ≫ Hmap (𝟙 _) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            Hmap (L.d p p') (𝟙 _)))
    (hπ₃ : ∀ (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ Hmap (f.f p) (g.f q))
    (m : ℤ) :
    ∃ iso : Functor.uncurry.obj F ⋙ shiftFunctor _ (-m) ≅
      ((shiftFunctor (CochainComplex A ℤ) m).op.prod (𝟭 _)) ⋙
        Functor.uncurry.obj F,
      ∀ (L M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q),
        (iso.app (op L, M)).hom.f k ≫ π (L⟦m⟧) M k p q h =
          (m * k).negOnePow • π L M (k + -m) (p + m) q (by omega) := by
  classical
  choose e he using fun L ↦
    ordinaryLeftShiftAux Hobj Hmap hid hsmul F π hπ₁ hπ₂ hπ₃ L m
  have hform (L M : CochainComplex A ℤ) (k p q : ℤ) (h : p + k = q) :
      ((e L).hom.app M).f k ≫ π (L⟦m⟧) M k p q h =
        (m * k).negOnePow • π L M (k + -m) (p + m) q (by omega) := by
    simpa only [Iso.app_hom, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      hid,
      Category.comp_id] using he L M k p q h
  refine ⟨NatIso.ofComponents (fun X ↦ (e X.1.unop).app X.2) ?_, ?_⟩
  · intro X Y f
    apply HomologicalComplex.hom_ext
    intro k
    apply Fan.IsLimit.hom_ext (Classical.choice (hπ₁ (Y.1.unop⟦m⟧) Y.2 k))
    intro p
    change (((F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2).f (k + -m) ≫
        ((e Y.1.unop).hom.app Y.2).f k) ≫
        π (Y.1.unop⟦m⟧) Y.2 k p (p + k) rfl =
      (((e X.1.unop).hom.app X.2).f k ≫
        ((F.map (((shiftFunctor _ m).map f.1.unop).op)).app X.2 ≫
          (F.obj (op (Y.1.unop⟦m⟧))).map f.2).f k) ≫
          π (Y.1.unop⟦m⟧) Y.2 k p (p + k) rfl
    rw [Category.assoc, hform, Linear.comp_units_smul]
    dsimp only [CochainComplex.shiftFunctor_obj_X']
    erw [hπ₃ X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2
      (k + -m) (p + m) (p + k) (by omega)]
    rw [Category.assoc,
      hπ₃ (X.1.unop⟦m⟧) (Y.1.unop⟦m⟧) X.2 Y.2
        ((shiftFunctor _ m).map f.1.unop) f.2 k p (p + k) rfl,
      ← Category.assoc, hform, Linear.units_smul_comp]
    rfl
  · intro L M k p q h
    exact hform L M k p q h

private abbrev ordinaryBifunctor :=
  Functor.uncurry.obj (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
set_option backward.isDefEq.respectTransparency true in
private theorem ordinaryLeftShift (s : ℤ) :
    ∃ iso : ordinaryBifunctor.{c, v, r} J R ⋙ shiftFunctor _ (-s) ≅
      ((shiftFunctor (Complex.{c, v, r} J R) s).op.prod (𝟭 _)) ⋙
        ordinaryBifunctor.{c, v, r} J R,
      ∀ (L F : Complex.{c, v, r} J R),
        LeftFormula.{c, v, r} J R L F s (iso.app (op L, F)) := by
  exact ordinaryLeftShiftBifunctorAux
    (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R))
    (fun {_X _X' _Y _Y'} f g ↦
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f g)
    (fun X Y ↦ SheafOfModules.homObjMap_id.{max c v r, v, c, max c v r}
      (R := R) (M := X) (N := Y))
    (fun {_X _X' _Y _Y'} a f g ↦ homObjMap_units_smul_left.{c, v, r} (R := R) a f g)
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R))
    (homComplexπ.{c, v, max c v r, max c v r} (R := R))
    (fun L F k ↦ ⟨homComplexIsLimit.{c, v, max c v r, max c v r} L F k⟩)
    (homComplex_d_π.{c, v, max c v r, max c v r} (R := R))
    (fun _ _ _ _ f g ↦ homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} f g) s

variable [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

set_option backward.isDefEq.respectTransparency true

/-- The existing ambient derived category.
Source: Stacks 08J7 (auxiliary; not a blueprint node). -/
abbrev D := DerivedCategory (Modules.{c, v, r} J R)

/-- The recorded derived internal Hom with its source fixed.
Source: Stacks 08J7 (auxiliary; not a blueprint node). -/
abbrev hom (M : D.{c, v, r, w} J R) : D.{c, v, r, w} J R ⥤ D.{c, v, r, w} J R :=
  (Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).obj (op M)

end CategoryTheory.RingedHomUniverses
