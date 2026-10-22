import Langlands.Cohomology.Tate.TensorBoundary
import Langlands.Cohomology.Tate.TensorExact
import Langlands.Cohomology.Tate.CupInvariant

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The actual connecting morphism with an explicitly specified successor degree. -/
def tateDeltaTo {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (n m : ℤ) (h : n + 1 = m) : tateCohomology S.X₃ n ⟶ tateCohomology S.X₁ m :=
  TateCohomology.δ hS n ≫ (tateDegreeIso S.X₁ h).hom

lemma tateDeltaTo_transport {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    {n n' m : ℤ} (hn : n = n') (hm : n + 1 = m) (hnm : n' + 1 = m) :
    TateCohomology.δ hS n ≫ (tateDegreeIso S.X₁ hm).hom =
      (tateDegreeIso S.X₃ hn).hom ≫ tateDeltaTo hS n' m hnm := by
  subst n'
  subst m
  simp [tateDeltaTo, tateDegreeIso]

lemma tateDegreeIso_inv (A : Rep.{u} R G) {m n : ℤ} (h : m = n) :
    (tateDegreeIso A h).inv = (tateDegreeIso A h.symm).hom := by
  subst n
  rfl

lemma tensorDeltaTo_anticommutes (S T : ShortComplex (Rep.{u} R G))
    (hTop : (T.map (MonoidalCategory.tensorLeft S.X₁)).ShortExact)
    (hBottom : (T.map (MonoidalCategory.tensorLeft S.X₃)).ShortExact)
    (hLeft : (S.map (MonoidalCategory.tensorRight T.X₁)).ShortExact)
    (hMiddle : (S.map (MonoidalCategory.tensorRight T.X₂)).ShortExact)
    (hRight : (S.map (MonoidalCategory.tensorRight T.X₃)).ShortExact)
    (n a b k : ℤ) (ha : n + 1 = a) (hb : n + 1 = b)
    (hak : a + 1 = k) (hbk : b + 1 = k) :
    tateDeltaTo hBottom n a ha ≫ tateDeltaTo hLeft a k hak =
      -(tateDeltaTo hRight n b hb ≫ tateDeltaTo hTop b k hbk) := by
  subst a
  subst b
  subst k
  simpa only [tateDeltaTo, tateDegreeIso, eqToIso_refl, Iso.refl_hom, Category.comp_id] using
    tensor_delta_anticommutes S T hTop hBottom hLeft hMiddle hRight n

lemma tensorCupSecondUpIso_hom (A B : Rep.{u} R G) (p : ℤ) (q : ℕ) :
    (tensorCupSecondUpIso A B p q).hom =
      tateDeltaTo
        (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) A)
        (p + q) (p + ((q + 1 : ℕ) : ℤ)) (by push_cast; omega) := rfl

lemma tensorCupSecondDownIso_inv (A B : Rep.{u} R G) (p : ℤ) (q : ℕ) :
    (tensorCupSecondDownIso A B p q).inv =
      tateDeltaTo
        (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) A)
        (p + -((q + 1 : ℕ) : ℤ)) (p + -(q : ℤ)) (by push_cast; omega) := by
  dsimp only [tensorCupSecondDownIso, Iso.trans_inv, Iso.symm_inv, tateDeltaTo]
  rw [tateDegreeIso_inv]
  rfl

lemma tensorDeltaTo_upRight (S : ShortComplex (Rep.{u} R G))
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p : ℤ) (q : ℕ) :
    (tensorCupSecondUpIso S.X₃ B p q).hom ≫
        tateDeltaTo hB (p + ((q + 1 : ℕ) : ℤ)) ((p + 1) + ((q + 1 : ℕ) : ℤ))
          (by omega) =
      -(tateDeltaTo (tensorShiftUp_shortExact S B hB) (p + q) ((p + 1) + q)
        (by omega) ≫ (tensorCupSecondUpIso S.X₁ B (p + 1) q).hom) := by
  rw [tensorCupSecondUpIso_hom, tensorCupSecondUpIso_hom]
  exact tensorDeltaTo_anticommutes S (shiftUpSequence B)
    (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) S.X₁)
    (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) S.X₃)
    hB (tensorCoinduced_shortExact S B hB) (tensorShiftUp_shortExact S B hB)
    _ _ _ _ _ _ _ _

lemma tensorDeltaTo_downRight (S : ShortComplex (Rep.{u} R G))
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p : ℤ) (q : ℕ) :
    (tensorCupSecondDownIso S.X₃ B p q).inv ≫
        tateDeltaTo (tensorShiftDown_shortExact S B hB)
          (p + -(q : ℤ)) ((p + 1) + -(q : ℤ)) (by omega) =
      -(tateDeltaTo hB (p + -((q + 1 : ℕ) : ℤ))
        ((p + 1) + -((q + 1 : ℕ) : ℤ)) (by omega) ≫
        (tensorCupSecondDownIso S.X₁ B (p + 1) q).inv) := by
  rw [tensorCupSecondDownIso_inv, tensorCupSecondDownIso_inv]
  exact tensorDeltaTo_anticommutes S (shiftDownSequence B)
    (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) S.X₁)
    (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) S.X₃)
    (tensorShiftDown_shortExact S B hB) (tensorCoinduced_shortExact S B hB) hB
    _ _ _ _ _ _ _ _

lemma tensorCupSecondNonneg_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p : ℤ) (q : ℕ) (x : tateCohomology S.X₃ p) (b : tateCohomology B q) :
    tensorCupSecondNonneg (p + 1) q S.X₁ B (TateCohomology.δ hS p x) b =
      tateDeltaTo hB (p + q) ((p + 1) + q) (by omega)
        (tensorCupSecondNonneg p q S.X₃ B x b) := by
  induction q generalizing B with
  | zero =>
    change (tateDegreeIso (S.X₁ ⊗ B) (show p + 1 = (p + 1) + (0 : ℕ) by omega)).hom
        (tensorCupFirst S.X₁ B (p + 1) (TateCohomology.δ hS p x) b) =
      tateDeltaTo hB _ _ _ ((tateDegreeIso (S.X₃ ⊗ B)
        (show p = p + (0 : ℕ) by omega)).hom (tensorCupFirst S.X₃ B p x b))
    rw [tensorCupFirst_delta]
    exact ConcreteCategory.congr_hom
      (tateDeltaTo_transport hB (show p = p + (0 : ℕ) by omega)
        (show p + 1 = (p + 1) + (0 : ℕ) by omega) (by omega))
      (tensorCupFirst S.X₃ B p x b)
  | succ q ih =>
    obtain ⟨b, rfl⟩ := (shiftUpIso B q).toLinearEquiv.surjective b
    change tensorCupSecondNonneg (p + 1) (q + 1) S.X₁ B
        (TateCohomology.δ hS p x) ((shiftUpIso B q).hom b) =
      tateDeltaTo hB (p + ((q + 1 : ℕ) : ℤ)) ((p + 1) + ((q + 1 : ℕ) : ℤ)) _
        (tensorCupSecondNonneg p (q + 1) S.X₃ B x ((shiftUpIso B q).hom b))
    rw [tensorCupSecondNonneg_shift, tensorCupSecondNonneg_shift,
      ih (shiftUp B) (tensorShiftUp_shortExact S B hB), map_zsmul]
    have ha := ConcreteCategory.congr_hom (tensorDeltaTo_upRight S B hB p q)
      (tensorCupSecondNonneg p q S.X₃ (shiftUp B) x b)
    change tateDeltaTo hB _ _ _
        ((tensorCupSecondUpIso S.X₃ B p q).hom
          (tensorCupSecondNonneg p q S.X₃ (shiftUp B) x b)) =
      -((tensorCupSecondUpIso S.X₁ B (p + 1) q).hom
        (tateDeltaTo (tensorShiftUp_shortExact S B hB) _ _ _
          (tensorCupSecondNonneg p q S.X₃ (shiftUp B) x b))) at ha
    rw [ha, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_neg]

lemma tensorCupSecondNonpos_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p : ℤ) (q : ℕ) (x : tateCohomology S.X₃ p) (b : tateCohomology B (-(q : ℤ))) :
    tensorCupSecondNonpos (p + 1) q S.X₁ B (TateCohomology.δ hS p x) b =
      tateDeltaTo hB (p + -(q : ℤ)) ((p + 1) + -(q : ℤ)) (by omega)
        (tensorCupSecondNonpos p q S.X₃ B x b) := by
  induction q generalizing B with
  | zero =>
    change (tateDegreeIso (S.X₁ ⊗ B) (show p + 1 = (p + 1) + -(0 : ℕ) by omega)).hom
        (tensorCupFirst S.X₁ B (p + 1) (TateCohomology.δ hS p x) b) =
      tateDeltaTo hB _ _ _ ((tateDegreeIso (S.X₃ ⊗ B)
        (show p = p + -(0 : ℕ) by omega)).hom (tensorCupFirst S.X₃ B p x b))
    rw [tensorCupFirst_delta]
    exact ConcreteCategory.congr_hom
      (tateDeltaTo_transport hB (show p = p + -(0 : ℕ) by omega)
        (show p + 1 = (p + 1) + -(0 : ℕ) by omega) (by omega))
      (tensorCupFirst S.X₃ B p x b)
  | succ q ih =>
    let e₁ := (tensorCupSecondDownIso S.X₁ B (p + 1) q).toLinearEquiv
    let e₃ := (tensorCupSecondDownIso S.X₃ B p q).toLinearEquiv
    apply e₁.symm.injective
    change e₁.symm (((p + 1).negOnePow : ℤ) • e₁
        (tensorCupSecondNonpos (p + 1) q S.X₁ (shiftDown B)
          (TateCohomology.δ hS p x) ((shiftDownNegativeIso B q).hom b))) =
      e₁.symm (tateDeltaTo hB _ _ _
        ((p.negOnePow : ℤ) • e₃
          (tensorCupSecondNonpos p q S.X₃ (shiftDown B) x
            ((shiftDownNegativeIso B q).hom b))))
    rw [map_zsmul, e₁.symm_apply_apply, map_zsmul, map_zsmul,
      ih (shiftDown B) (tensorShiftDown_shortExact S B hB)]
    let c := tensorCupSecondNonpos p q S.X₃ (shiftDown B) x
      ((shiftDownNegativeIso B q).hom b)
    have ha := ConcreteCategory.congr_hom (tensorDeltaTo_downRight S B hB p q) (e₃ c)
    change tateDeltaTo (tensorShiftDown_shortExact S B hB) _ _ _ (e₃.symm (e₃ c)) =
      -(e₁.symm (tateDeltaTo hB _ _ _ (e₃ c))) at ha
    rw [e₃.symm_apply_apply] at ha
    have hb : e₁.symm (tateDeltaTo hB _ _ _ (e₃ c)) =
        -(tateDeltaTo (tensorShiftDown_shortExact S B hB) _ _ _ c) :=
      (neg_neg _).symm.trans (congrArg Neg.neg ha.symm)
    change ((p + 1).negOnePow : ℤ) •
        tateDeltaTo (tensorShiftDown_shortExact S B hB) _ _ _ c =
      (p.negOnePow : ℤ) • e₁.symm (tateDeltaTo hB _ _ _ (e₃ c))
    rw [hb, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_neg]

/-- The first-variable boundary law in every integer bidegree, with exactly tensor exactness. -/
lemma tensorCup_delta_first (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p q : ℤ) (x : tateCohomology S.X₃ p) (b : tateCohomology B q) :
    tensorCup S.X₁ B (p + 1) q (TateCohomology.δ hS p x) b =
      tateDeltaTo hB (p + q) ((p + 1) + q) (by omega)
        (tensorCup S.X₃ B p q x b) := by
  cases q with
  | ofNat q => exact tensorCupSecondNonneg_delta S hS B hB p q x b
  | negSucc q => exact tensorCupSecondNonpos_delta S hS B hB p (q + 1) x b

end Langlands.Tate
