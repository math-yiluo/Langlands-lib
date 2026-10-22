import Langlands.Cohomology.Tate.CupDefinitions
import Langlands.Cohomology.Tate.TensorNaturality
import Langlands.Cohomology.Tate.ZeroProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

lemma tateDegreeIso_naturality {A B : Rep.{u} R G} (f : A ⟶ B)
    {m n : ℤ} (h : m = n) :
    (tateDegreeIso A h).hom ≫ (tateCohomologyFunctor n).map f =
      (tateCohomologyFunctor m).map f ≫ (tateDegreeIso B h).hom := by
  subst n
  simp [tateDegreeIso]

lemma inverse_naturality {C : Type*} [Category C] {X X' Y Y' : C}
    (e : X ≅ Y) (e' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : e.hom ≫ g = f ≫ e'.hom) :
    e.inv ≫ f = g ≫ e'.inv := by
  apply e.inv_comp_eq.mpr
  rw [← Category.assoc, h]
  simp

lemma tensorCup_zero_zero (A B : Rep.{u} R G) :
    tensorCup A B 0 0 = cupZero (tensorPairing A B) := by
  ext a b
  rfl

lemma cup_zero_zero {A B C : Rep.{u} R G} (φ : Pairing A B C) :
    cup φ 0 0 = cupZero φ := by
  ext a b
  change (tateCohomologyFunctor 0).map φ.tensorHom (tensorCup A B 0 0 a b) =
    cupZero φ a b
  rw [tensorCup_zero_zero]
  simpa using cupZero_naturality (tensorPairing A B) φ (𝟙 A) (𝟙 B) φ.tensorHom
    (fun _ _ => rfl) a b

lemma cup_zeroClass {A B C : Rep.{u} R G} (φ : Pairing A B C)
    (a : A.ρ.invariants) (b : B.ρ.invariants) :
    cup φ 0 0 (zeroClass A a) (zeroClass B b) =
      zeroClass C (φ.onInvariants a b) := by
  rw [cup_zero_zero]
  exact cupZero_zeroClass φ a b

lemma tensorCupFirstNonneg_naturality (p : ℕ)
    {A A' B B' : Rep.{u} R G} (f : A ⟶ A') (g : B ⟶ B')
    (a : tateCohomology A p) (b : tateCohomology B 0) :
    (tateCohomologyFunctor p).map (f ⊗ₘ g) (tensorCupFirstNonneg p A B a b) =
      tensorCupFirstNonneg p A' B' ((tateCohomologyFunctor p).map f a)
        ((tateCohomologyFunctor 0).map g b) := by
  induction p generalizing A A' B B' with
  | zero =>
      exact cupZero_naturality (tensorPairing A B) (tensorPairing A' B')
        f g (f ⊗ₘ g) (fun a b => TensorProduct.map_tmul _ _ a b) a b
  | succ p ih =>
      change (tateCohomologyFunctor (p + 1)).map (f ⊗ₘ g)
          ((tensorShiftUpLeftIso A B p).hom
            (tensorCupFirstNonneg p (shiftUp A) B ((shiftUpIso A p).inv a) b)) =
        (tensorShiftUpLeftIso A' B' p).hom
          (tensorCupFirstNonneg p (shiftUp A') B'
            ((shiftUpIso A' p).inv ((tateCohomologyFunctor (p + 1)).map f a))
            ((tateCohomologyFunctor 0).map g b))
      refine (ConcreteCategory.congr_hom (tensorShiftUpLeftIso_naturality f g p)
        (tensorCupFirstNonneg p (shiftUp A) B ((shiftUpIso A p).inv a) b)).trans ?_
      apply congrArg (tensorShiftUpLeftIso A' B' p).hom
      refine (ih (shiftUpMap f) g ((shiftUpIso A p).inv a) b).trans ?_
      apply congrArg (fun x => tensorCupFirstNonneg p (shiftUp A') B' x
        ((tateCohomologyFunctor 0).map g b))
      exact ConcreteCategory.congr_hom
          (inverse_naturality (shiftUpIso A p) (shiftUpIso A' p)
            ((tateCohomologyFunctor p).map (shiftUpMap f))
            ((tateCohomologyFunctor (p + 1)).map f) (shiftUpIso_naturality f p)) a

lemma tensorShiftDownLeftNegativeIso_naturality
    {A A' B B' : Rep.{u} R G} (f : A ⟶ A') (g : B ⟶ B') (n : ℕ) :
    (tensorShiftDownLeftNegativeIso A B n).hom ≫
        (tateCohomologyFunctor (-(n : ℤ))).map (shiftDownMap f ⊗ₘ g) =
      (tateCohomologyFunctor (-(n + 1 : ℤ))).map (f ⊗ₘ g) ≫
        (tensorShiftDownLeftNegativeIso A' B' n).hom := by
  dsimp only [tensorShiftDownLeftNegativeIso, Iso.trans_hom]
  rw [Category.assoc, tateDegreeIso_naturality, ← Category.assoc,
    tensorShiftDownLeftIso_naturality, Category.assoc]

lemma shiftDownNegativeIso_naturality
    {A A' : Rep.{u} R G} (f : A ⟶ A') (n : ℕ) :
    (shiftDownNegativeIso A n).hom ≫
        (tateCohomologyFunctor (-(n : ℤ))).map (shiftDownMap f) =
      (tateCohomologyFunctor (-(n + 1 : ℤ))).map f ≫
        (shiftDownNegativeIso A' n).hom := by
  change ((shiftDownIso A (-(n + 1 : ℤ))).hom ≫
      (tateDegreeIso (shiftDown A) (show -(n + 1 : ℤ) + 1 = -(n : ℤ) by omega)).hom) ≫
      (tateCohomologyFunctor (-(n : ℤ))).map (shiftDownMap f) = _
  rw [Category.assoc, tateDegreeIso_naturality, ← Category.assoc,
    shiftDownIso_naturality, Category.assoc]
  rfl

lemma tensorCupFirstNonpos_naturality (p : ℕ)
    {A A' B B' : Rep.{u} R G} (f : A ⟶ A') (g : B ⟶ B')
    (a : tateCohomology A (-(p : ℤ))) (b : tateCohomology B 0) :
    (tateCohomologyFunctor (-(p : ℤ))).map (f ⊗ₘ g)
        (tensorCupFirstNonpos p A B a b) =
      tensorCupFirstNonpos p A' B' ((tateCohomologyFunctor (-(p : ℤ))).map f a)
        ((tateCohomologyFunctor 0).map g b) := by
  induction p generalizing A A' B B' with
  | zero =>
      exact cupZero_naturality (tensorPairing A B) (tensorPairing A' B')
        f g (f ⊗ₘ g) (fun a b => TensorProduct.map_tmul _ _ a b) a b
  | succ p ih =>
      change (tateCohomologyFunctor (-(p + 1 : ℤ))).map (f ⊗ₘ g)
          ((tensorShiftDownLeftNegativeIso A B p).inv
            (tensorCupFirstNonpos p (shiftDown A) B ((shiftDownNegativeIso A p).hom a) b)) =
        (tensorShiftDownLeftNegativeIso A' B' p).inv
          (tensorCupFirstNonpos p (shiftDown A') B'
            ((shiftDownNegativeIso A' p).hom
              ((tateCohomologyFunctor (-(p + 1 : ℤ))).map f a))
            ((tateCohomologyFunctor 0).map g b))
      refine (ConcreteCategory.congr_hom
        (inverse_naturality (tensorShiftDownLeftNegativeIso A B p)
          (tensorShiftDownLeftNegativeIso A' B' p)
          ((tateCohomologyFunctor (-(p + 1 : ℤ))).map (f ⊗ₘ g))
          ((tateCohomologyFunctor (-(p : ℤ))).map (shiftDownMap f ⊗ₘ g))
          (tensorShiftDownLeftNegativeIso_naturality f g p))
          (tensorCupFirstNonpos p (shiftDown A) B ((shiftDownNegativeIso A p).hom a) b)).trans ?_
      apply congrArg (tensorShiftDownLeftNegativeIso A' B' p).inv
      refine (ih (shiftDownMap f) g ((shiftDownNegativeIso A p).hom a) b).trans ?_
      apply congrArg (fun x => tensorCupFirstNonpos p (shiftDown A') B' x
        ((tateCohomologyFunctor 0).map g b))
      exact ConcreteCategory.congr_hom (shiftDownNegativeIso_naturality f p) a

lemma tensorCupFirst_naturality (p : ℤ)
    {A A' B B' : Rep.{u} R G} (f : A ⟶ A') (g : B ⟶ B')
    (a : tateCohomology A p) (b : tateCohomology B 0) :
    (tateCohomologyFunctor p).map (f ⊗ₘ g) (tensorCupFirst A B p a b) =
      tensorCupFirst A' B' p ((tateCohomologyFunctor p).map f a)
        ((tateCohomologyFunctor 0).map g b) := by
  cases p with
  | ofNat p => exact tensorCupFirstNonneg_naturality p f g a b
  | negSucc p => exact tensorCupFirstNonpos_naturality (p + 1) f g a b

/-- The second positive tensor connecting isomorphism with the total degree made explicit. -/
abbrev tensorCupSecondUpIso (A B : Rep.{u} R G) (p : ℤ) (q : ℕ) :
    tateCohomology (A ⊗ shiftUp B) (p + q) ≅
      tateCohomology (A ⊗ B) (p + ((q + 1 : ℕ) : ℤ)) :=
  tensorShiftUpRightIso A B (p + q) ≪≫ tateDegreeIso _ (by push_cast; omega)

/-- The second negative tensor connecting isomorphism with the total degree made explicit. -/
abbrev tensorCupSecondDownIso (A B : Rep.{u} R G) (p : ℤ) (q : ℕ) :
    tateCohomology (A ⊗ shiftDown B) (p + -(q : ℤ)) ≅
      tateCohomology (A ⊗ B) (p + -((q + 1 : ℕ) : ℤ)) :=
  tateDegreeIso _ (show p + -(q : ℤ) = (p + -((q + 1 : ℕ) : ℤ)) + 1 by push_cast; omega) ≪≫
    (tensorShiftDownRightIso A B (p + -((q + 1 : ℕ) : ℤ))).symm

lemma tensorCupSecondUpIso_naturality {A A' B B' : Rep.{u} R G}
    (f : A ⟶ A') (g : B ⟶ B') (p : ℤ) (q : ℕ) :
    (tensorCupSecondUpIso A B p q).hom ≫
        (tateCohomologyFunctor (p + ((q + 1 : ℕ) : ℤ))).map (f ⊗ₘ g) =
      (tateCohomologyFunctor (p + q)).map (f ⊗ₘ shiftUpMap g) ≫
        (tensorCupSecondUpIso A' B' p q).hom := by
  dsimp only [tensorCupSecondUpIso, Iso.trans_hom]
  rw [Category.assoc, tateDegreeIso_naturality, ← Category.assoc,
    tensorShiftUpRightIso_naturality, Category.assoc]

lemma tensorCupSecondDownIso_naturality {A A' B B' : Rep.{u} R G}
    (f : A ⟶ A') (g : B ⟶ B') (p : ℤ) (q : ℕ) :
    (tensorCupSecondDownIso A B p q).hom ≫
        (tateCohomologyFunctor (p + -((q + 1 : ℕ) : ℤ))).map (f ⊗ₘ g) =
      (tateCohomologyFunctor (p + -(q : ℤ))).map (f ⊗ₘ shiftDownMap g) ≫
        (tensorCupSecondDownIso A' B' p q).hom := by
  dsimp only [tensorCupSecondDownIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, inverse_naturality _ _ _ _
    (tensorShiftDownRightIso_naturality f g (p + -((q + 1 : ℕ) : ℤ))),
    ← Category.assoc, tateDegreeIso_naturality, Category.assoc]

lemma tensorCupSecondNonneg_naturality (p : ℤ) (q : ℕ)
    {A A' B B' : Rep.{u} R G} (f : A ⟶ A') (g : B ⟶ B')
    (a : tateCohomology A p) (b : tateCohomology B q) :
    (tateCohomologyFunctor (p + q)).map (f ⊗ₘ g) (tensorCupSecondNonneg p q A B a b) =
      tensorCupSecondNonneg p q A' B' ((tateCohomologyFunctor p).map f a)
        ((tateCohomologyFunctor q).map g b) := by
  induction q generalizing A A' B B' with
  | zero =>
      refine (ConcreteCategory.congr_hom
        (tateDegreeIso_naturality (f ⊗ₘ g) (show p = p + (0 : ℕ) by simp))
        (tensorCupFirst A B p a b)).trans ?_
      exact congrArg (tateDegreeIso (A' ⊗ B') (show p = p + (0 : ℕ) by simp)).hom
        (tensorCupFirst_naturality p f g a b)
  | succ q ih =>
      change (tateCohomologyFunctor (p + ((q + 1 : ℕ) : ℤ))).map (f ⊗ₘ g)
          ((p.negOnePow : ℤ) • (tensorCupSecondUpIso A B p q).hom
            (tensorCupSecondNonneg p q A (shiftUp B) a ((shiftUpIso B q).inv b))) =
        (p.negOnePow : ℤ) • (tensorCupSecondUpIso A' B' p q).hom
          (tensorCupSecondNonneg p q A' (shiftUp B') ((tateCohomologyFunctor p).map f a)
            ((shiftUpIso B' q).inv ((tateCohomologyFunctor (q + 1)).map g b)))
      rw [map_zsmul]
      apply congrArg ((p.negOnePow : ℤ) • ·)
      refine (ConcreteCategory.congr_hom (tensorCupSecondUpIso_naturality f g p q)
        (tensorCupSecondNonneg p q A (shiftUp B) a ((shiftUpIso B q).inv b))).trans ?_
      apply congrArg (tensorCupSecondUpIso A' B' p q).hom
      refine (ih f (shiftUpMap g) a ((shiftUpIso B q).inv b)).trans ?_
      apply congrArg (tensorCupSecondNonneg p q A' (shiftUp B')
        ((tateCohomologyFunctor p).map f a))
      exact ConcreteCategory.congr_hom
        (inverse_naturality (shiftUpIso B q) (shiftUpIso B' q)
          ((tateCohomologyFunctor q).map (shiftUpMap g))
          ((tateCohomologyFunctor (q + 1)).map g) (shiftUpIso_naturality g q)) b

lemma tensorCupSecondNonpos_naturality (p : ℤ) (q : ℕ)
    {A A' B B' : Rep.{u} R G} (f : A ⟶ A') (g : B ⟶ B')
    (a : tateCohomology A p) (b : tateCohomology B (-(q : ℤ))) :
    (tateCohomologyFunctor (p + -(q : ℤ))).map (f ⊗ₘ g)
        (tensorCupSecondNonpos p q A B a b) =
      tensorCupSecondNonpos p q A' B' ((tateCohomologyFunctor p).map f a)
        ((tateCohomologyFunctor (-(q : ℤ))).map g b) := by
  induction q generalizing A A' B B' with
  | zero =>
      refine (ConcreteCategory.congr_hom
        (tateDegreeIso_naturality (f ⊗ₘ g) (show p = p + -(0 : ℕ) by simp))
        (tensorCupFirst A B p a b)).trans ?_
      exact congrArg (tateDegreeIso (A' ⊗ B') (show p = p + -(0 : ℕ) by simp)).hom
        (tensorCupFirst_naturality p f g a b)
  | succ q ih =>
      change (tateCohomologyFunctor (p + -((q + 1 : ℕ) : ℤ))).map (f ⊗ₘ g)
          ((p.negOnePow : ℤ) • (tensorCupSecondDownIso A B p q).hom
            (tensorCupSecondNonpos p q A (shiftDown B) a ((shiftDownNegativeIso B q).hom b))) =
        (p.negOnePow : ℤ) • (tensorCupSecondDownIso A' B' p q).hom
          (tensorCupSecondNonpos p q A' (shiftDown B') ((tateCohomologyFunctor p).map f a)
            ((shiftDownNegativeIso B' q).hom
              ((tateCohomologyFunctor (-(q + 1 : ℤ))).map g b)))
      rw [map_zsmul]
      apply congrArg ((p.negOnePow : ℤ) • ·)
      refine (ConcreteCategory.congr_hom (tensorCupSecondDownIso_naturality f g p q)
        (tensorCupSecondNonpos p q A (shiftDown B) a ((shiftDownNegativeIso B q).hom b))).trans ?_
      apply congrArg (tensorCupSecondDownIso A' B' p q).hom
      refine (ih f (shiftDownMap g) a ((shiftDownNegativeIso B q).hom b)).trans ?_
      apply congrArg (tensorCupSecondNonpos p q A' (shiftDown B')
        ((tateCohomologyFunctor p).map f a))
      exact ConcreteCategory.congr_hom (shiftDownNegativeIso_naturality g q) b

lemma tensorCup_naturality (p q : ℤ)
    {A A' B B' : Rep.{u} R G} (f : A ⟶ A') (g : B ⟶ B')
    (a : tateCohomology A p) (b : tateCohomology B q) :
    (tateCohomologyFunctor (p + q)).map (f ⊗ₘ g) (tensorCup A B p q a b) =
      tensorCup A' B' p q ((tateCohomologyFunctor p).map f a)
        ((tateCohomologyFunctor q).map g b) := by
  cases q with
  | ofNat q => exact tensorCupSecondNonneg_naturality p q f g a b
  | negSucc q => exact tensorCupSecondNonpos_naturality p (q + 1) f g a b

omit [Fintype G] in
lemma Pairing.tensorHom_naturality
    {A A' B B' C C' : Rep.{u} R G} (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (hφ : ∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b)) :
    φ.tensorHom ≫ h = (f ⊗ₘ g) ≫ φ'.tensorHom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro a b
  exact hφ a b

lemma cup_naturality (p q : ℤ)
    {A A' B B' C C' : Rep.{u} R G} (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (hφ : ∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b))
    (a : tateCohomology A p) (b : tateCohomology B q) :
    (tateCohomologyFunctor (p + q)).map h (cup φ p q a b) =
      cup φ' p q ((tateCohomologyFunctor p).map f a)
        ((tateCohomologyFunctor q).map g b) := by
  have hm :
      (tateCohomologyFunctor (p + q)).map φ.tensorHom ≫
          (tateCohomologyFunctor (p + q)).map h =
        (tateCohomologyFunctor (p + q)).map (f ⊗ₘ g) ≫
          (tateCohomologyFunctor (p + q)).map φ'.tensorHom := by
    calc
      _ = (tateCohomologyFunctor (p + q)).map (φ.tensorHom ≫ h) :=
        ((tateCohomologyFunctor (p + q)).map_comp φ.tensorHom h).symm
      _ = (tateCohomologyFunctor (p + q)).map ((f ⊗ₘ g) ≫ φ'.tensorHom) :=
        congrArg (tateCohomologyFunctor (p + q)).map (φ.tensorHom_naturality φ' f g h hφ)
      _ = _ := (tateCohomologyFunctor (p + q)).map_comp (f ⊗ₘ g) φ'.tensorHom
  change (tateCohomologyFunctor (p + q)).map h
      ((tateCohomologyFunctor (p + q)).map φ.tensorHom (tensorCup A B p q a b)) =
    (tateCohomologyFunctor (p + q)).map φ'.tensorHom
      (tensorCup A' B' p q ((tateCohomologyFunctor p).map f a)
        ((tateCohomologyFunctor q).map g b))
  refine (ConcreteCategory.congr_hom hm (tensorCup A B p q a b)).trans ?_
  have hn := tensorCup_naturality p q f g a b
  exact congrArg
    (fun x : tateCohomology (A' ⊗ B') (p + q) =>
      (((tateCohomologyFunctor (p + q)).map φ'.tensorHom).hom x :
        tateCohomology C' (p + q))) hn

lemma tensorCupFirstNonneg_shift (A B : Rep.{u} R G) (p : ℕ)
    (a : tateCohomology (shiftUp A) p) (b : tateCohomology B 0) :
    tensorCupFirstNonneg (p + 1) A B ((shiftUpIso A p).hom a) b =
      (tensorShiftUpLeftIso A B p).hom (tensorCupFirstNonneg p (shiftUp A) B a b) := by
  change (tensorShiftUpLeftIso A B p).hom
    (tensorCupFirstNonneg p (shiftUp A) B
      ((shiftUpIso A p).toLinearEquiv.symm ((shiftUpIso A p).toLinearEquiv a)) b) = _
  rw [LinearEquiv.symm_apply_apply]

lemma tensorCupFirstNonpos_shift (A B : Rep.{u} R G) (p : ℕ)
    (a : tateCohomology A (-(p + 1 : ℤ))) (b : tateCohomology B 0) :
    (tensorShiftDownLeftNegativeIso A B p).hom (tensorCupFirstNonpos (p + 1) A B a b) =
      tensorCupFirstNonpos p (shiftDown A) B ((shiftDownNegativeIso A p).hom a) b :=
  (tensorShiftDownLeftNegativeIso A B p).toLinearEquiv.apply_symm_apply _

lemma tensorCupSecondNonneg_shift (A B : Rep.{u} R G) (p : ℤ) (q : ℕ)
    (a : tateCohomology A p) (b : tateCohomology (shiftUp B) q) :
    tensorCupSecondNonneg p (q + 1) A B a ((shiftUpIso B q).hom b) =
      (p.negOnePow : ℤ) • (tensorCupSecondUpIso A B p q).hom
        (tensorCupSecondNonneg p q A (shiftUp B) a b) := by
  change (p.negOnePow : ℤ) • (tensorCupSecondUpIso A B p q).hom
    (tensorCupSecondNonneg p q A (shiftUp B) a
      ((shiftUpIso B q).toLinearEquiv.symm ((shiftUpIso B q).toLinearEquiv b))) = _
  rw [LinearEquiv.symm_apply_apply]

lemma tensorCupSecondNonpos_shift (A B : Rep.{u} R G) (p : ℤ) (q : ℕ)
    (a : tateCohomology A p) (b : tateCohomology B (-(q + 1 : ℤ))) :
    tensorCupSecondNonpos p q A (shiftDown B) a ((shiftDownNegativeIso B q).hom b) =
      (p.negOnePow : ℤ) • (tensorCupSecondDownIso A B p q).inv
        (tensorCupSecondNonpos p (q + 1) A B a b) := by
  let x := tensorCupSecondNonpos p q A (shiftDown B) a ((shiftDownNegativeIso B q).hom b)
  let e := (tensorCupSecondDownIso A B p q).toLinearEquiv
  change x = (p.negOnePow : ℤ) • e.symm ((p.negOnePow : ℤ) • e x)
  rw [map_zsmul, e.symm_apply_apply, ← mul_smul]
  have hs : (p.negOnePow : ℤ) * (p.negOnePow : ℤ) = 1 :=
    congrArg Units.val (Int.units_mul_self p.negOnePow)
  rw [hs, one_smul]

end Langlands.Tate
