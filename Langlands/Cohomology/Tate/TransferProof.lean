import Langlands.Cohomology.Tate.TransferDefinitions
import Langlands.Cohomology.Tate.ZeroProof

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

def shiftUpNatIso (n : ℤ) :
    shiftUpFunctor (R := R) (G := G) ⋙ tateCohomologyFunctor n ≅
      tateCohomologyFunctor (n + 1) :=
  NatIso.ofComponents (fun A => shiftUpIso A n) (fun f => (shiftUpIso_naturality f n).symm)

def shiftDownNatIso (n : ℤ) :
    tateCohomologyFunctor n ≅
      shiftDownFunctor (R := R) (G := G) ⋙ tateCohomologyFunctor (n + 1) :=
  NatIso.ofComponents (fun A => shiftDownIso A n) (fun f => (shiftDownIso_naturality f n).symm)

def restrictedShiftUpNatIso (n : ℤ) :
    shiftUpFunctor (R := R) ⋙ Rep.resFunctor H.subtype ⋙ tateCohomologyFunctor n ≅
      Rep.resFunctor H.subtype ⋙ tateCohomologyFunctor (n + 1) :=
  NatIso.ofComponents (fun A => restrictedShiftUpIso (R := R) H A n)
    (fun f => (restrictedShiftUpIso_naturality H f n).symm)

def restrictedShiftDownNatIso (n : ℤ) :
    Rep.resFunctor (k := R) H.subtype ⋙ tateCohomologyFunctor n ≅
      shiftDownFunctor ⋙ Rep.resFunctor H.subtype ⋙ tateCohomologyFunctor (n + 1) :=
  NatIso.ofComponents (fun A => restrictedShiftDownIso (R := R) H A n)
    (fun f => (restrictedShiftDownIso_naturality H f n).symm)

def shiftDownNegativeNatIso (n : ℕ) :
    tateCohomologyFunctor (-(n + 1 : ℤ)) ≅
      shiftDownFunctor (R := R) (G := G) ⋙ tateCohomologyFunctor (-(n : ℤ)) :=
  shiftDownNatIso (-(n + 1 : ℤ)) ≪≫
    eqToIso (congrArg (fun i => shiftDownFunctor ⋙ tateCohomologyFunctor i) (by omega))

def restrictedShiftDownNegativeNatIso (n : ℕ) :
    Rep.resFunctor H.subtype ⋙ tateCohomologyFunctor (-(n + 1 : ℤ)) ≅
      shiftDownFunctor (R := R) ⋙ Rep.resFunctor H.subtype ⋙
        tateCohomologyFunctor (-(n : ℤ)) :=
  restrictedShiftDownNatIso H (-(n + 1 : ℤ)) ≪≫
    eqToIso (congrArg (fun i => shiftDownFunctor ⋙ Rep.resFunctor H.subtype ⋙
      tateCohomologyFunctor i) (by omega))

lemma shiftDownNegativeNatIso_app (n : ℕ) (A : Rep.{u} R G) :
    (shiftDownNegativeNatIso n).app A = shiftDownNegativeIso A n := by
  ext
  simp [shiftDownNegativeNatIso, shiftDownNegativeIso, shiftDownNatIso]
  rfl

omit [Fintype (G ⧸ H)] in
lemma restrictedShiftDownNegativeNatIso_app (n : ℕ) (A : Rep.{u} R G) :
    (restrictedShiftDownNegativeNatIso H n).app A = restrictedShiftDownNegativeIso H A n := by
  ext
  simp [restrictedShiftDownNegativeNatIso, restrictedShiftDownNegativeIso,
    restrictedShiftDownNatIso]
  rfl

def restrictionZeroNat :
    tateCohomologyFunctor 0 ⟶ Rep.resFunctor (k := R) H.subtype ⋙ tateCohomologyFunctor 0 where
  app A := ModuleCat.ofHom (restrictionZero H A)
  naturality _ _ f := by
    ext x
    exact (restrictionZero_naturality H f x).symm

def corestrictionZeroNat :
    Rep.resFunctor (k := R) H.subtype ⋙ tateCohomologyFunctor 0 ⟶ tateCohomologyFunctor 0 where
  app A := ModuleCat.ofHom (corestrictionZero H A)
  naturality _ _ f := by
    ext x
    exact (corestrictionZero_naturality H f x).symm

def restrictionNonnegNat : (n : ℕ) →
    tateCohomologyFunctor n ⟶ Rep.resFunctor (k := R) H.subtype ⋙ tateCohomologyFunctor n
  | 0 => restrictionZeroNat H
  | n + 1 => (shiftUpNatIso n).inv ≫
      Functor.whiskerLeft shiftUpFunctor (restrictionNonnegNat n) ≫
      (restrictedShiftUpNatIso H n).hom

def corestrictionNonnegNat : (n : ℕ) →
    Rep.resFunctor (k := R) H.subtype ⋙ tateCohomologyFunctor n ⟶ tateCohomologyFunctor n
  | 0 => corestrictionZeroNat H
  | n + 1 => (restrictedShiftUpNatIso H n).inv ≫
      Functor.whiskerLeft shiftUpFunctor (corestrictionNonnegNat n) ≫
      (shiftUpNatIso n).hom

def restrictionNonposNat : (n : ℕ) →
    tateCohomologyFunctor (-(n : ℤ)) ⟶
      Rep.resFunctor (k := R) H.subtype ⋙ tateCohomologyFunctor (-(n : ℤ))
  | 0 => restrictionZeroNat H
  | n + 1 => (shiftDownNegativeNatIso n).hom ≫
      Functor.whiskerLeft shiftDownFunctor (restrictionNonposNat n) ≫
      (restrictedShiftDownNegativeNatIso H n).inv

def corestrictionNonposNat : (n : ℕ) →
    Rep.resFunctor (k := R) H.subtype ⋙ tateCohomologyFunctor (-(n : ℤ)) ⟶
      tateCohomologyFunctor (-(n : ℤ))
  | 0 => corestrictionZeroNat H
  | n + 1 => (restrictedShiftDownNegativeNatIso H n).hom ≫
      Functor.whiskerLeft shiftDownFunctor (corestrictionNonposNat n) ≫
      (shiftDownNegativeNatIso n).inv

lemma restrictionNonnegNat_app (n : ℕ) (A : Rep.{u} R G) :
    (restrictionNonnegNat H n).app A = ModuleCat.ofHom (restrictionNonneg H n A) := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [restrictionNonnegNat, NatTrans.comp_app, Functor.whiskerLeft_app, ih]
    rfl

lemma corestrictionNonnegNat_app (n : ℕ) (A : Rep.{u} R G) :
    (corestrictionNonnegNat H n).app A = ModuleCat.ofHom (corestrictionNonneg H n A) := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [corestrictionNonnegNat, NatTrans.comp_app, Functor.whiskerLeft_app, ih]
    rfl

lemma restrictionNonposNat_app (n : ℕ) (A : Rep.{u} R G) :
    (restrictionNonposNat H n).app A = ModuleCat.ofHom (restrictionNonpos H n A) := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [restrictionNonposNat, NatTrans.comp_app, Functor.whiskerLeft_app, ih]
    change ((shiftDownNegativeNatIso n).app A).hom ≫
      ModuleCat.ofHom (restrictionNonpos H n (shiftDown A)) ≫
      ((restrictedShiftDownNegativeNatIso H n).app A).inv = _
    rw [shiftDownNegativeNatIso_app, restrictedShiftDownNegativeNatIso_app]
    rfl

lemma corestrictionNonposNat_app (n : ℕ) (A : Rep.{u} R G) :
    (corestrictionNonposNat H n).app A = ModuleCat.ofHom (corestrictionNonpos H n A) := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    simp only [corestrictionNonposNat, NatTrans.comp_app, Functor.whiskerLeft_app, ih]
    change ((restrictedShiftDownNegativeNatIso H n).app A).hom ≫
      ModuleCat.ofHom (corestrictionNonpos H n (shiftDown A)) ≫
      ((shiftDownNegativeNatIso n).app A).inv = _
    rw [shiftDownNegativeNatIso_app, restrictedShiftDownNegativeNatIso_app]
    rfl

lemma restrictionNonneg_naturality (n : ℕ) {A B : Rep.{u} R G}
    (f : A ⟶ B) (x : tateCohomology A n) :
    (tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map f)
        (restrictionNonneg H n A x) =
      restrictionNonneg H n B ((tateCohomologyFunctor n).map f x) := by
  have h := (restrictionNonnegNat H n).naturality f
  rw [restrictionNonnegNat_app, restrictionNonnegNat_app] at h
  exact (ConcreteCategory.congr_hom h x).symm

lemma corestrictionNonneg_naturality (n : ℕ) {A B : Rep.{u} R G}
    (f : A ⟶ B) (x : tateCohomology (Rep.res H.subtype A) n) :
    (tateCohomologyFunctor n).map f (corestrictionNonneg H n A x) =
      corestrictionNonneg H n B
        ((tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map f) x) := by
  have h := (corestrictionNonnegNat H n).naturality f
  rw [corestrictionNonnegNat_app, corestrictionNonnegNat_app] at h
  exact (ConcreteCategory.congr_hom h x).symm

lemma restrictionNonpos_naturality (n : ℕ) {A B : Rep.{u} R G}
    (f : A ⟶ B) (x : tateCohomology A (-(n : ℤ))) :
    (tateCohomologyFunctor (-(n : ℤ))).map ((Rep.resFunctor H.subtype).map f)
        (restrictionNonpos H n A x) =
      restrictionNonpos H n B ((tateCohomologyFunctor (-(n : ℤ))).map f x) := by
  have h := (restrictionNonposNat H n).naturality f
  rw [restrictionNonposNat_app, restrictionNonposNat_app] at h
  exact (ConcreteCategory.congr_hom h x).symm

lemma corestrictionNonpos_naturality (n : ℕ) {A B : Rep.{u} R G}
    (f : A ⟶ B) (x : tateCohomology (Rep.res H.subtype A) (-(n : ℤ))) :
    (tateCohomologyFunctor (-(n : ℤ))).map f (corestrictionNonpos H n A x) =
      corestrictionNonpos H n B
        ((tateCohomologyFunctor (-(n : ℤ))).map ((Rep.resFunctor H.subtype).map f) x) := by
  have h := (corestrictionNonposNat H n).naturality f
  rw [corestrictionNonposNat_app, corestrictionNonposNat_app] at h
  exact (ConcreteCategory.congr_hom h x).symm

/-- Coefficient naturality for the actual Tate functors in every integer degree. -/
lemma restriction_naturality (n : ℤ) {A B : Rep.{u} R G}
    (f : A ⟶ B) (x : tateCohomology A n) :
    (tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map f)
        (restriction H A n x) =
      restriction H B n ((tateCohomologyFunctor n).map f x) := by
  cases n with
  | ofNat n => exact restrictionNonneg_naturality H n f x
  | negSucc n => exact restrictionNonpos_naturality H (n + 1) f x

/-- Coefficient naturality for corestriction in every integer degree. -/
lemma corestriction_naturality (n : ℤ) {A B : Rep.{u} R G}
    (f : A ⟶ B) (x : tateCohomology (Rep.res H.subtype A) n) :
    (tateCohomologyFunctor n).map f (corestriction H A n x) =
      corestriction H B n
        ((tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map f) x) := by
  cases n with
  | ofNat n => exact corestrictionNonneg_naturality H n f x
  | negSucc n => exact corestrictionNonpos_naturality H (n + 1) f x

lemma restrictionNonneg_shift (n : ℕ) (A : Rep.{u} R G)
    (x : tateCohomology (shiftUp A) n) :
    restrictionNonneg H (n + 1) A ((shiftUpIso A n).hom x) =
      (restrictedShiftUpIso H A n).hom (restrictionNonneg H n (shiftUp A) x) := by
  let e := (shiftUpIso A n).toLinearEquiv
  let d := (restrictedShiftUpIso H A n).toLinearEquiv
  change d (restrictionNonneg H n (shiftUp A) (e.symm (e x))) = _
  rw [e.symm_apply_apply]
  rfl

lemma corestrictionNonneg_shift (n : ℕ) (A : Rep.{u} R G)
    (x : tateCohomology (Rep.res H.subtype (shiftUp A)) n) :
    corestrictionNonneg H (n + 1) A ((restrictedShiftUpIso H A n).hom x) =
      (shiftUpIso A n).hom (corestrictionNonneg H n (shiftUp A) x) := by
  let e := (shiftUpIso A n).toLinearEquiv
  let d := (restrictedShiftUpIso H A n).toLinearEquiv
  change e (corestrictionNonneg H n (shiftUp A) (d.symm (d x))) = _
  rw [d.symm_apply_apply]
  rfl

lemma restrictionNonpos_shift (n : ℕ) (A : Rep.{u} R G)
    (x : tateCohomology A (-(n + 1 : ℤ))) :
    (restrictedShiftDownNegativeIso H A n).hom (restrictionNonpos H (n + 1) A x) =
      restrictionNonpos H n (shiftDown A) ((shiftDownNegativeIso A n).hom x) := by
  let e := (shiftDownNegativeIso A n).toLinearEquiv
  let d := (restrictedShiftDownNegativeIso H A n).toLinearEquiv
  change d (d.symm (restrictionNonpos H n (shiftDown A) (e x))) = _
  rw [d.apply_symm_apply]
  rfl

lemma corestrictionNonpos_shift (n : ℕ) (A : Rep.{u} R G)
    (x : tateCohomology (Rep.res H.subtype A) (-(n + 1 : ℤ))) :
    (shiftDownNegativeIso A n).hom (corestrictionNonpos H (n + 1) A x) =
      corestrictionNonpos H n (shiftDown A) ((restrictedShiftDownNegativeIso H A n).hom x) := by
  let e := (shiftDownNegativeIso A n).toLinearEquiv
  let d := (restrictedShiftDownNegativeIso H A n).toLinearEquiv
  change e (e.symm (corestrictionNonpos H n (shiftDown A) (d x))) = _
  rw [e.apply_symm_apply]
  rfl

lemma corestrictionNonneg_restrictionNonneg (n : ℕ) (A : Rep.{u} R G)
    (x : tateCohomology A n) :
    corestrictionNonneg H n A (restrictionNonneg H n A x) = H.index • x := by
  induction n generalizing A with
  | zero => exact corestrictionZero_restrictionZero H x
  | succ n ih =>
    let e := (shiftUpIso A n).toLinearEquiv
    let d := (restrictedShiftUpIso H A n).toLinearEquiv
    change e (corestrictionNonneg H n (shiftUp A)
      (d.symm (d (restrictionNonneg H n (shiftUp A) (e.symm x))))) = H.index • x
    rw [d.symm_apply_apply, ih, map_nsmul, e.apply_symm_apply]

lemma corestrictionNonpos_restrictionNonpos (n : ℕ) (A : Rep.{u} R G)
    (x : tateCohomology A (-(n : ℤ))) :
    corestrictionNonpos H n A (restrictionNonpos H n A x) = H.index • x := by
  induction n generalizing A with
  | zero => exact corestrictionZero_restrictionZero H x
  | succ n ih =>
    let e := (shiftDownNegativeIso A n).toLinearEquiv
    let d := (restrictedShiftDownNegativeIso H A n).toLinearEquiv
    change e.symm (corestrictionNonpos H n (shiftDown A)
      (d (d.symm (restrictionNonpos H n (shiftDown A) (e x))))) = H.index • x
    rw [d.apply_symm_apply, ih, map_nsmul, e.symm_apply_apply]

/-- The constructed corestriction after restriction is index multiplication in every degree. -/
lemma corestriction_restriction (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    corestriction H A n (restriction H A n x) = H.index • x := by
  cases n with
  | ofNat n => exact corestrictionNonneg_restrictionNonneg H n A x
  | negSucc n => exact corestrictionNonpos_restrictionNonpos H (n + 1) A x

end Langlands.Tate
