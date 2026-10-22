import Langlands.Cohomology.Tate.ShiftInduction
import Langlands.Cohomology.Tate.CupBoundarySecond
import Langlands.Cohomology.Tate.SplitTransfer

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

lemma tensorCup_invariantRight (A B : Rep.{u} R G) (p : ℤ)
    (a : tateCohomology A p) (b : B.ρ.invariants) :
    tensorCup A B p 0 a (zeroClass B b) =
      (tateDegreeIso (A ⊗ B) (show p = p + 0 by omega)).hom
        ((tateCohomologyFunctor p).map (tensorInvariantRight A B b) a) := by
  change (tateDegreeIso (A ⊗ B) (show p = p + 0 by omega)).hom
    (tensorCupFirst A B p a (zeroClass B b)) = _
  rw [tensorCupFirst_invariant]

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

lemma restriction_deltaTo (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (n m : ℤ) (h : n + 1 = m) (x : tateCohomology S.X₃ n) :
    restriction H S.X₁ m (tateDeltaTo (scalarSplit_shortExact S s) n m h x) =
      tateDeltaTo ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype))
        n m h (restriction H S.X₃ n x) := by
  subst m
  simpa only [tateDeltaTo, tateDegreeIso, eqToIso_refl, Iso.refl_hom, Category.comp_id] using
    restriction_scalarSplit_delta H S s n x

lemma corestriction_deltaTo (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (n m : ℤ) (h : n + 1 = m) (x : tateCohomology (Rep.res H.subtype S.X₃) n) :
    corestriction H S.X₁ m
        (tateDeltaTo ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype))
          n m h x) =
      tateDeltaTo (scalarSplit_shortExact S s) n m h (corestriction H S.X₃ n x) := by
  subst m
  simpa only [tateDeltaTo, tateDegreeIso, eqToIso_refl, Iso.refl_hom, Category.comp_id] using
    corestriction_scalarSplit_delta H S s n x

omit [Fintype G] [Fintype H] [Fintype (G ⧸ H)] in
lemma restrict_tensorInvariantRight (A B : Rep.{u} R G) (b : B.ρ.invariants) :
    (Rep.resFunctor H.subtype).map (tensorInvariantRight A B b) =
      tensorInvariantRight (Rep.res H.subtype A) (Rep.res H.subtype B)
        (invariantRestriction H B b) := rfl

lemma tensorCup_restriction_zero (A B : Rep.{u} R G) (p : ℤ)
    (a : tateCohomology A p) (b : tateCohomology B 0) :
    restriction H (A ⊗ B) (p + 0) (tensorCup A B p 0 a b) =
      tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p 0
        (restriction H A p a) (restriction H B 0 b) := by
  obtain ⟨b, rfl⟩ := zeroClass_surjective B b
  change _ = tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p 0
    (restriction H A p a) (restrictionZero H B (zeroClass B b))
  rw [restrictionZero_zeroClass, tensorCup_invariantRight, tensorCup_invariantRight]
  refine (restriction_degreeTransport H (A ⊗ B) (show p = p + 0 by omega)
    ((tateCohomologyFunctor p).map (tensorInvariantRight A B b) a)).trans ?_
  exact congrArg
    (tateDegreeIso (Rep.res H.subtype (A ⊗ B)) (show p = p + 0 by omega)).hom
    (restriction_naturality H p (tensorInvariantRight A B b) a).symm

lemma tensorCup_corestriction_zero (A B : Rep.{u} R G) (p : ℤ)
    (a : tateCohomology (Rep.res H.subtype A) p) (b : tateCohomology B 0) :
    corestriction H (A ⊗ B) (p + 0)
        (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p 0
          a (restriction H B 0 b)) =
      tensorCup A B p 0 (corestriction H A p a) b := by
  obtain ⟨b, rfl⟩ := zeroClass_surjective B b
  change corestriction H (A ⊗ B) (p + 0)
    (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p 0
      a (restrictionZero H B (zeroClass B b))) = _
  rw [restrictionZero_zeroClass, tensorCup_invariantRight, tensorCup_invariantRight]
  refine (corestriction_degreeTransport H (A ⊗ B) (show p = p + 0 by omega)
    ((tateCohomologyFunctor p).map
      ((Rep.resFunctor H.subtype).map (tensorInvariantRight A B b)) a)).trans ?_
  exact congrArg (tateDegreeIso (A ⊗ B) (show p = p + 0 by omega)).hom
    (corestriction_naturality H p (tensorInvariantRight A B b) a).symm

omit [Fintype G] [Fintype H] [Fintype (G ⧸ H)] in
lemma restricted_tensorLeft_shortExact (S : ShortComplex (Rep.{u} R G))
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    ((S.map (Rep.resFunctor H.subtype)).map
      (MonoidalCategory.tensorLeft (Rep.res H.subtype A))).ShortExact := by
  change ((S.map (MonoidalCategory.tensorLeft A)).map (Rep.resFunctor H.subtype)).ShortExact
  exact hA.map_of_exact _

omit [Fintype (G ⧸ H)] in
lemma restrictedTensorCoinduced_tate_isZero (A B : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology (Rep.res H.subtype (A ⊗ coinduced B)) n) :=
  (restrictedCoinduced_tate_isZero H (B ⊗ A) n).of_iso
    ((tateCohomologyFunctor n).mapIso ((Rep.resFunctor H.subtype).mapIso
      ((β_ A (coinduced B)) ≪≫ coinducedTensorIso B A)))

/-- The actual tensor augmentation boundary remains invertible after subgroup restriction. -/
def restrictedTensorShiftDownIso (A B : Rep.{u} R G) (n : ℤ) :
    tateCohomology (Rep.res H.subtype (A ⊗ B)) n ≅
      tateCohomology (Rep.res H.subtype (A ⊗ shiftDown B)) (n + 1) := by
  let hS := (scalarSplit_tensorLeft_shortExact _
    (shiftDownSequence_scalarSplitting B) A).map_of_exact (Rep.resFunctor H.subtype)
  have := tate_delta_isIso hS n
    (restrictedTensorCoinduced_tate_isZero H A B n)
    (restrictedTensorCoinduced_tate_isZero H A B (n + 1))
  exact asIso (TateCohomology.δ hS n)

lemma tensorCup_restriction_boundary (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (A : Rep.{u} R G) (p q : ℤ) (a : tateCohomology A p) (b : tateCohomology S.X₃ q) :
    restriction H (A ⊗ S.X₁) (p + (q + 1))
        (tensorCup A S.X₁ p (q + 1) a (TateCohomology.δ (scalarSplit_shortExact S s) q b)) =
      (p.negOnePow : ℤ) •
        tateDeltaTo ((scalarSplit_tensorLeft_shortExact S s A).map_of_exact
          (Rep.resFunctor H.subtype)) (p + q) (p + (q + 1)) (by omega)
          (restriction H (A ⊗ S.X₃) (p + q) (tensorCup A S.X₃ p q a b)) := by
  rw [tensorCup_delta_second S (scalarSplit_shortExact S s) A
    (scalarSplit_tensorLeft_shortExact S s A), map_zsmul]
  exact congrArg (fun x => (p.negOnePow : ℤ) • x)
    (restriction_deltaTo H (S.map (MonoidalCategory.tensorLeft A))
      (scalarSplitting_tensorLeft S s A) (p + q) (p + (q + 1)) (by omega)
      (tensorCup A S.X₃ p q a b))

lemma tensorCup_restricted_boundary (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (A : Rep.{u} R G) (p q : ℤ)
    (a : tateCohomology (Rep.res H.subtype A) p) (b : tateCohomology S.X₃ q) :
    tensorCup (Rep.res H.subtype A) (Rep.res H.subtype S.X₁) p (q + 1) a
        (restriction H S.X₁ (q + 1) (TateCohomology.δ (scalarSplit_shortExact S s) q b)) =
      (p.negOnePow : ℤ) •
        tateDeltaTo ((scalarSplit_tensorLeft_shortExact S s A).map_of_exact
          (Rep.resFunctor H.subtype)) (p + q) (p + (q + 1)) (by omega)
          (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype S.X₃) p q a
            (restriction H S.X₃ q b)) := by
  rw [restriction_scalarSplit_delta H S s q b]
  exact tensorCup_delta_second (S.map (Rep.resFunctor H.subtype))
    ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype))
    (Rep.res H.subtype A)
    (restricted_tensorLeft_shortExact H S A (scalarSplit_tensorLeft_shortExact S s A))
    p q a (restriction H S.X₃ q b)

/-- Restriction preserves the constructed tensor cup in every integer bidegree. -/
lemma tensorCup_restriction (A B : Rep.{u} R G) (p q : ℤ)
    (a : tateCohomology A p) (b : tateCohomology B q) :
    restriction H (A ⊗ B) (p + q) (tensorCup A B p q a b) =
      tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q
        (restriction H A p a) (restriction H B q b) := by
  refine tateClass_shift_induction
    (fun B q b => restriction H (A ⊗ B) (p + q) (tensorCup A B p q a b) =
      tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q
        (restriction H A p a) (restriction H B q b))
    (fun B b => tensorCup_restriction_zero H A B p a b) ?_ ?_ B q b
  · intro B q b ih
    refine (tensorCup_restriction_boundary H (shiftUpSequence B)
      (shiftUpSequence_scalarSplitting B) A p q a b).trans ?_
    refine Eq.trans ?_ (tensorCup_restricted_boundary H (shiftUpSequence B)
      (shiftUpSequence_scalarSplitting B) A p q (restriction H A p a) b).symm
    exact congrArg (fun x => (p.negOnePow : ℤ) •
      tateDeltaTo ((scalarSplit_tensorLeft_shortExact _
        (shiftUpSequence_scalarSplitting B) A).map_of_exact (Rep.resFunctor H.subtype))
        (p + q) (p + (q + 1)) (by omega) x) ih
  · intro B q b ih
    let e := restrictedTensorShiftDownIso H A B (p + q) ≪≫
      tateDegreeIso (Rep.res H.subtype (A ⊗ shiftDown B))
        (show (p + q) + 1 = p + (q + 1) by omega)
    apply e.toLinearEquiv.injective
    have hb := (tensorCup_restriction_boundary H (shiftDownSequence B)
      (shiftDownSequence_scalarSplitting B) A p q a b).symm.trans
        (ih.trans (tensorCup_restricted_boundary H (shiftDownSequence B)
          (shiftDownSequence_scalarSplitting B) A p q (restriction H A p a) b))
    have hh := congrArg (fun x => (p.negOnePow : ℤ) • x) hb
    have hs : (p.negOnePow : ℤ) * (p.negOnePow : ℤ) = 1 :=
      congrArg Units.val (Int.units_mul_self p.negOnePow)
    simp only [smul_smul, hs, one_smul] at hh
    exact hh

lemma tensorCup_corestriction_boundary (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (A : Rep.{u} R G) (p q : ℤ)
    (a : tateCohomology (Rep.res H.subtype A) p) (b : tateCohomology S.X₃ q) :
    corestriction H (A ⊗ S.X₁) (p + (q + 1))
        (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype S.X₁) p (q + 1) a
          (restriction H S.X₁ (q + 1) (TateCohomology.δ (scalarSplit_shortExact S s) q b))) =
      (p.negOnePow : ℤ) •
        tateDeltaTo (scalarSplit_tensorLeft_shortExact S s A)
          (p + q) (p + (q + 1)) (by omega)
          (corestriction H (A ⊗ S.X₃) (p + q)
            (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype S.X₃) p q a
              (restriction H S.X₃ q b))) := by
  refine (congrArg (corestriction H (A ⊗ S.X₁) (p + (q + 1)))
    (tensorCup_restricted_boundary H S s A p q a b)).trans ?_
  rw [map_zsmul]
  exact congrArg (fun x => (p.negOnePow : ℤ) • x)
    (corestriction_deltaTo H (S.map (MonoidalCategory.tensorLeft A))
      (scalarSplitting_tensorLeft S s A) (p + q) (p + (q + 1)) (by omega)
      (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype S.X₃) p q a
        (restriction H S.X₃ q b)))

/-- The tensor projection formula in every integer bidegree. -/
lemma tensorCup_corestriction (A B : Rep.{u} R G) (p q : ℤ)
    (a : tateCohomology (Rep.res H.subtype A) p) (b : tateCohomology B q) :
    corestriction H (A ⊗ B) (p + q)
        (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q a
          (restriction H B q b)) =
      tensorCup A B p q (corestriction H A p a) b := by
  refine tateClass_shift_induction
    (fun B q b => corestriction H (A ⊗ B) (p + q)
      (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q a
        (restriction H B q b)) = tensorCup A B p q (corestriction H A p a) b)
    (fun B b => tensorCup_corestriction_zero H A B p a b) ?_ ?_ B q b
  · intro B q b ih
    refine (tensorCup_corestriction_boundary H (shiftUpSequence B)
      (shiftUpSequence_scalarSplitting B) A p q a b).trans ?_
    refine Eq.trans ?_ (tensorCup_delta_second (shiftUpSequence B)
      (shiftUpSequence_shortExact B) A
      (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) A)
      p q (corestriction H A p a) b).symm
    exact congrArg (fun x => (p.negOnePow : ℤ) •
      tateDeltaTo (scalarSplit_tensorLeft_shortExact _
        (shiftUpSequence_scalarSplitting B) A) (p + q) (p + (q + 1)) (by omega) x) ih
  · intro B q b ih
    let e := tensorShiftDownRightIso A B (p + q) ≪≫
      tateDegreeIso (A ⊗ shiftDown B) (show (p + q) + 1 = p + (q + 1) by omega)
    apply e.toLinearEquiv.injective
    have hb := (tensorCup_corestriction_boundary H (shiftDownSequence B)
      (shiftDownSequence_scalarSplitting B) A p q a b).symm.trans
        (ih.trans (tensorCup_delta_second (shiftDownSequence B)
          (shiftDownSequence_shortExact B) A
          (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) A)
          p q (corestriction H A p a) b))
    have hh := congrArg (fun x => (p.negOnePow : ℤ) • x) hb
    have hs : (p.negOnePow : ℤ) * (p.negOnePow : ℤ) = 1 :=
      congrArg Units.val (Int.units_mul_self p.negOnePow)
    simp only [smul_smul, hs, one_smul] at hh
    exact hh

/-- Restriction compatibility for every equivariant bilinear coefficient pairing. -/
lemma cup_restriction {A B C : Rep.{u} R G} (φ : Pairing A B C) (p q : ℤ)
    (a : tateCohomology A p) (b : tateCohomology B q) :
    restriction H C (p + q) (cup φ p q a b) =
      cup (φ.restrict H) p q (restriction H A p a) (restriction H B q b) := by
  refine (restriction_naturality H (p + q) φ.tensorHom (tensorCup A B p q a b)).symm.trans ?_
  exact congrArg
    (fun x => (tateCohomologyFunctor (p + q)).map ((Rep.resFunctor H.subtype).map φ.tensorHom) x)
    (tensorCup_restriction H A B p q a b)

/-- Corestriction projection for every equivariant bilinear coefficient pairing. -/
lemma cup_corestriction {A B C : Rep.{u} R G} (φ : Pairing A B C) (p q : ℤ)
    (a : tateCohomology (Rep.res H.subtype A) p) (b : tateCohomology B q) :
    corestriction H C (p + q) (cup (φ.restrict H) p q a (restriction H B q b)) =
      cup φ p q (corestriction H A p a) b := by
  refine (corestriction_naturality H (p + q) φ.tensorHom
    (tensorCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q a
      (restriction H B q b))).symm.trans ?_
  exact congrArg (fun x => (tateCohomologyFunctor (p + q)).map φ.tensorHom x)
    (tensorCup_corestriction H A B p q a b)

end Langlands.Tate
