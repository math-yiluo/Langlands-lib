import Langlands.Cohomology.Tate.CupBoundary

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- Tensoring with an invariant first vector is an equivariant coefficient map. -/
def tensorInvariantLeft (A B : Rep.{u} R G) (a : A.ρ.invariants) : B ⟶ A ⊗ B :=
  Rep.ofHom ⟨TensorProduct.mk R A B a, fun g => by
    ext b
    change (a : A) ⊗ₜ[R] (B.ρ g b) = (A.ρ g a) ⊗ₜ[R] (B.ρ g b)
    rw [a.property g]⟩

lemma tensorInvariantLeft_naturality (A : Rep.{u} R G) (a : A.ρ.invariants)
    {B B' : Rep.{u} R G} (f : B ⟶ B') :
    f ≫ tensorInvariantLeft A B' a = tensorInvariantLeft A B a ≫ (𝟙 A ⊗ₘ f) := by
  ext b
  rfl

def tensorInvariantLeftSequence (S : ShortComplex (Rep.{u} R G))
    (A : Rep.{u} R G) (a : A.ρ.invariants) :
    S ⟶ S.map (MonoidalCategory.tensorLeft A) where
  τ₁ := tensorInvariantLeft A S.X₁ a
  τ₂ := tensorInvariantLeft A S.X₂ a
  τ₃ := tensorInvariantLeft A S.X₃ a
  comm₁₂ := (tensorInvariantLeft_naturality A a S.f).symm
  comm₂₃ := (tensorInvariantLeft_naturality A a S.g).symm

variable [Fintype G]

lemma tateDeltaTo_naturality {S T : ShortComplex (Rep.{u} R G)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T)
    (n m : ℤ) (h : n + 1 = m) :
    tateDeltaTo hS n m h ≫ (tateCohomologyFunctor m).map f.τ₁ =
      (tateCohomologyFunctor n).map f.τ₃ ≫ tateDeltaTo hT n m h := by
  subst m
  simpa [tateDeltaTo, tateDegreeIso] using TateCohomology.δ_naturality hS hT f n

lemma tateDeltaTo_degreeSquare {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    {n n' m m' : ℤ} (hn : n = n') (hm : m = m') (h : n + 1 = m) (h' : n' + 1 = m') :
    tateDeltaTo hS n m h ≫ (tateDegreeIso S.X₁ hm).hom =
      (tateDegreeIso S.X₃ hn).hom ≫ tateDeltaTo hS n' m' h' := by
  subst n'
  subst m'
  simp [tateDegreeIso]

lemma invariantLeft_boundary_square (S : ShortComplex (Rep.{u} R G))
    (hS : S.ShortExact) (A : Rep.{u} R G)
    (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact) (a : A.ρ.invariants)
    (n m : ℤ) (h : n + 1 = m) :
    tateDeltaTo hS n m h ≫ (tateCohomologyFunctor m).map (tensorInvariantLeft A S.X₁ a) ≫
        (tateDegreeIso (A ⊗ S.X₁) (show m = 0 + m by omega)).hom =
      (tateCohomologyFunctor n).map (tensorInvariantLeft A S.X₃ a) ≫
        (tateDegreeIso (A ⊗ S.X₃) (show n = 0 + n by omega)).hom ≫
        tateDeltaTo hA (0 + n) (0 + m) (by omega) := by
  have hn :
      tateDeltaTo hS n m h ≫ (tateCohomologyFunctor m).map (tensorInvariantLeft A S.X₁ a) =
        (tateCohomologyFunctor n).map (tensorInvariantLeft A S.X₃ a) ≫
          tateDeltaTo hA n m h :=
    tateDeltaTo_naturality hS hA (tensorInvariantLeftSequence S A a) n m h
  have hd :
      tateDeltaTo hA n m h ≫ (tateDegreeIso (A ⊗ S.X₁) (show m = 0 + m by omega)).hom =
        (tateDegreeIso (A ⊗ S.X₃) (show n = 0 + n by omega)).hom ≫
          tateDeltaTo hA (0 + n) (0 + m) (by omega) :=
    tateDeltaTo_degreeSquare hA (show n = 0 + n by omega)
      (show m = 0 + m by omega) h (by omega)
  rw [← Category.assoc, hn, Category.assoc, hd]

lemma tensorCupSecondNonneg_invariantLeft (q : ℕ) (A B : Rep.{u} R G)
    (a : A.ρ.invariants) (b : tateCohomology B q) :
    tensorCupSecondNonneg 0 q A B (zeroClass A a) b =
      (tateDegreeIso (A ⊗ B) (show (q : ℤ) = 0 + q by omega)).hom
        ((tateCohomologyFunctor q).map (tensorInvariantLeft A B a) b) := by
  induction q generalizing B with
  | zero =>
    obtain ⟨b, rfl⟩ := zeroClass_surjective B b
    change cupZero (tensorPairing A B) (zeroClass A a) (zeroClass B b) =
      (tateCohomologyFunctor 0).map (tensorInvariantLeft A B a) (zeroClass B b)
    rw [cupZero_zeroClass]
    exact (zeroClass_naturality (tensorInvariantLeft A B a) b).symm
  | succ q ih =>
    obtain ⟨b, rfl⟩ := (shiftUpIso B q).toLinearEquiv.surjective b
    change tensorCupSecondNonneg 0 (q + 1) A B (zeroClass A a) ((shiftUpIso B q).hom b) = _
    rw [tensorCupSecondNonneg_shift, ih]
    simp only [Int.negOnePow_zero, Units.val_one, one_smul]
    exact (ConcreteCategory.congr_hom
      (invariantLeft_boundary_square (shiftUpSequence B) (shiftUpSequence_shortExact B) A
        (scalarSplit_tensorLeft_shortExact _ (shiftUpSequence_scalarSplitting B) A)
        a q (q + 1) rfl) b).symm

lemma tensorCupSecondNonpos_invariantLeft (q : ℕ) (A B : Rep.{u} R G)
    (a : A.ρ.invariants) (b : tateCohomology B (-(q : ℤ))) :
    tensorCupSecondNonpos 0 q A B (zeroClass A a) b =
      (tateDegreeIso (A ⊗ B) (show -(q : ℤ) = 0 + -(q : ℤ) by omega)).hom
        ((tateCohomologyFunctor (-(q : ℤ))).map (tensorInvariantLeft A B a) b) := by
  induction q generalizing B with
  | zero => exact tensorCupSecondNonneg_invariantLeft 0 A B a b
  | succ q ih =>
    apply (tensorCupSecondDownIso A B 0 q).toLinearEquiv.symm.injective
    change (tensorCupSecondDownIso A B 0 q).inv
        (tensorCupSecondNonpos 0 (q + 1) A B (zeroClass A a) b) =
      (tensorCupSecondDownIso A B 0 q).inv
        ((tateDegreeIso (A ⊗ B) _).hom
          ((tateCohomologyFunctor (-(q + 1 : ℤ))).map (tensorInvariantLeft A B a) b))
    have h := tensorCupSecondNonpos_shift A B 0 q (zeroClass A a) b
    simp only [Int.negOnePow_zero, Units.val_one, one_smul] at h
    rw [← h, ih]
    exact ConcreteCategory.congr_hom
      (invariantLeft_boundary_square (shiftDownSequence B) (shiftDownSequence_shortExact B) A
        (scalarSplit_tensorLeft_shortExact _ (shiftDownSequence_scalarSplitting B) A)
        a (-(q + 1 : ℤ)) (-(q : ℤ)) (by omega)) b

/-- Multiplication by an invariant first class is the actual coefficient map in all second degrees. -/
lemma tensorCup_invariantLeft (A B : Rep.{u} R G) (q : ℤ) (a : A.ρ.invariants)
    (b : tateCohomology B q) :
    tensorCup A B 0 q (zeroClass A a) b =
      (tateDegreeIso (A ⊗ B) (show q = 0 + q by omega)).hom
        ((tateCohomologyFunctor q).map (tensorInvariantLeft A B a) b) := by
  cases q with
  | ofNat q => exact tensorCupSecondNonneg_invariantLeft q A B a b
  | negSucc q => exact tensorCupSecondNonpos_invariantLeft (q + 1) A B a b

lemma tensorCup_delta_second_zero (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (q : ℤ) (a : tateCohomology A 0) (b : tateCohomology S.X₃ q) :
    tensorCup A S.X₁ 0 (q + 1) a (TateCohomology.δ hS q b) =
      tateDeltaTo hA (0 + q) (0 + (q + 1)) (by omega)
        (tensorCup A S.X₃ 0 q a b) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective A a
  rw [tensorCup_invariantLeft, tensorCup_invariantLeft]
  exact ConcreteCategory.congr_hom
    (invariantLeft_boundary_square S hS A hA a q (q + 1) rfl) b

/-- The first boundary law with a specified equality for the successor degree. -/
lemma tensorCup_delta_first_to (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p m q : ℤ) (h : p + 1 = m)
    (a : tateCohomology S.X₃ p) (b : tateCohomology B q) :
    tensorCup S.X₁ B m q (tateDeltaTo hS p m h a) b =
      tateDeltaTo hB (p + q) (m + q) (by omega) (tensorCup S.X₃ B p q a b) := by
  subst m
  change tensorCup S.X₁ B (p + 1) q (TateCohomology.δ hS p a) b = _
  exact tensorCup_delta_first S hS B hB p q a b

/-- First-variable tensor shift, with both source and target degrees specified. -/
def tensorFirstUpIso (A B : Rep.{u} R G) (p m q : ℤ) (h : p + 1 = m) :
    tateCohomology (shiftUp A ⊗ B) (p + q) ≅ tateCohomology (A ⊗ B) (m + q) :=
  tensorShiftUpLeftIso A B (p + q) ≪≫ tateDegreeIso _ (by omega)

/-- Negative first-variable tensor shift, with its target degree specified. -/
def tensorFirstDownIso (A B : Rep.{u} R G) (p m q : ℤ) (h : p + 1 = m) :
    tateCohomology (A ⊗ B) (p + q) ≅ tateCohomology (shiftDown A ⊗ B) (m + q) :=
  tensorShiftDownLeftIso A B (p + q) ≪≫ tateDegreeIso _ (by omega)

lemma tensorFirstUpIso_hom (A B : Rep.{u} R G) (p m q : ℤ) (h : p + 1 = m) :
    (tensorFirstUpIso A B p m q h).hom =
      tateDeltaTo (scalarSplit_tensorRight_shortExact _
        (shiftUpSequence_scalarSplitting A) B) (p + q) (m + q) (by omega) := rfl

lemma tensorFirstDownIso_hom (A B : Rep.{u} R G) (p m q : ℤ) (h : p + 1 = m) :
    (tensorFirstDownIso A B p m q h).hom =
      tateDeltaTo (scalarSplit_tensorRight_shortExact _
        (shiftDownSequence_scalarSplitting A) B) (p + q) (m + q) (by omega) := rfl

lemma tensorDeltaTo_upLeft (S : ShortComplex (Rep.{u} R G))
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p m q : ℤ) (h : p + 1 = m) :
    tateDeltaTo (shiftUpTensor_shortExact S A hA) (p + q) (p + (q + 1)) (by omega) ≫
        (tensorFirstUpIso A S.X₁ p m (q + 1) h).hom =
      -((tensorFirstUpIso A S.X₃ p m q h).hom ≫
        tateDeltaTo hA (m + q) (m + (q + 1)) (by omega)) := by
  exact tensorDeltaTo_anticommutes (shiftUpSequence A) S
    hA (shiftUpTensor_shortExact S A hA)
    (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) S.X₁)
    (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) S.X₂)
    (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) S.X₃)
    _ _ _ _ _ _ _ _

lemma tensorDeltaTo_downLeft (S : ShortComplex (Rep.{u} R G))
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p m q : ℤ) (h : p + 1 = m) :
    tateDeltaTo hA (p + q) (p + (q + 1)) (by omega) ≫
        (tensorFirstDownIso A S.X₁ p m (q + 1) h).hom =
      -((tensorFirstDownIso A S.X₃ p m q h).hom ≫
        tateDeltaTo (shiftDownTensor_shortExact S A hA) (m + q) (m + (q + 1)) (by omega)) := by
  exact tensorDeltaTo_anticommutes (shiftDownSequence A) S
    (shiftDownTensor_shortExact S A hA) hA
    (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) S.X₁)
    (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) S.X₂)
    (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) S.X₃)
    _ _ _ _ _ _ _ _

lemma tensorCup_delta_second_nonneg (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p : ℕ) (q : ℤ) (a : tateCohomology A p) (b : tateCohomology S.X₃ q) :
    tensorCup A S.X₁ p (q + 1) a (TateCohomology.δ hS q b) =
      ((p : ℤ).negOnePow : ℤ) • tateDeltaTo hA (p + q) (p + (q + 1)) (by omega)
        (tensorCup A S.X₃ p q a b) := by
  induction p generalizing A with
  | zero =>
    change tensorCup A S.X₁ 0 (q + 1) a (TateCohomology.δ hS q b) =
      ((0 : ℤ).negOnePow : ℤ) •
        tateDeltaTo hA (0 + q) (0 + (q + 1)) (by omega) (tensorCup A S.X₃ 0 q a b)
    simpa only [Nat.cast_zero, Int.negOnePow_zero, Units.val_one, one_smul] using
      tensorCup_delta_second_zero S hS A hA q a b
  | succ p ih =>
    let e := shiftUpIso A p ≪≫ tateDegreeIso A (show (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ) by omega)
    obtain ⟨a, rfl⟩ := e.toLinearEquiv.surjective a
    change tensorCup A S.X₁ (p + 1 : ℕ) (q + 1)
        (tateDeltaTo (shiftUpSequence_shortExact A) p (p + 1 : ℕ) (by omega) a)
        (TateCohomology.δ hS q b) =
      (((p + 1 : ℕ) : ℤ).negOnePow : ℤ) • tateDeltaTo hA _ _ _
        (tensorCup A S.X₃ (p + 1 : ℕ) q
          (tateDeltaTo (shiftUpSequence_shortExact A) p (p + 1 : ℕ) (by omega) a) b)
    rw [tensorCup_delta_first_to (shiftUpSequence A) (shiftUpSequence_shortExact A) S.X₁
        (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) S.X₁),
      tensorCup_delta_first_to (shiftUpSequence A) (shiftUpSequence_shortExact A) S.X₃
        (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) S.X₃),
      ih (shiftUp A) (shiftUpTensor_shortExact S A hA), map_zsmul]
    have hd := tensorDeltaTo_upLeft S A hA p (p + 1 : ℕ) q (by omega)
    rw [tensorFirstUpIso_hom, tensorFirstUpIso_hom] at hd
    have ha := ConcreteCategory.congr_hom hd (tensorCup (shiftUp A) S.X₃ p q a b)
    change tateDeltaTo (scalarSplit_tensorRight_shortExact _
        (shiftUpSequence_scalarSplitting A) S.X₁) (p + (q + 1)) ((p + 1 : ℕ) + (q + 1)) _
        (tateDeltaTo (shiftUpTensor_shortExact S A hA) (p + q) (p + (q + 1)) _
          (tensorCup (shiftUp A) S.X₃ p q a b)) =
      -(tateDeltaTo hA ((p + 1 : ℕ) + q) ((p + 1 : ℕ) + (q + 1)) _
        (tateDeltaTo (scalarSplit_tensorRight_shortExact _
          (shiftUpSequence_scalarSplitting A) S.X₃) (p + q) ((p + 1 : ℕ) + q) _
          (tensorCup (shiftUp A) S.X₃ p q a b))) at ha
    have hs : ((((p + 1 : ℕ) : ℤ)).negOnePow : ℤ) = -((p : ℤ).negOnePow : ℤ) := by
      rw [Nat.cast_add, Nat.cast_one, Int.negOnePow_succ, Units.val_neg]
    rw [ha, hs, smul_neg, neg_smul]

lemma tensorCup_delta_second_nonpos (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p : ℕ) (q : ℤ) (a : tateCohomology A (-(p : ℤ))) (b : tateCohomology S.X₃ q) :
    tensorCup A S.X₁ (-(p : ℤ)) (q + 1) a (TateCohomology.δ hS q b) =
      ((-(p : ℤ)).negOnePow : ℤ) • tateDeltaTo hA (-(p : ℤ) + q) (-(p : ℤ) + (q + 1))
        (by omega) (tensorCup A S.X₃ (-(p : ℤ)) q a b) := by
  induction p generalizing A with
  | zero =>
    change tensorCup A S.X₁ 0 (q + 1) a (TateCohomology.δ hS q b) =
      ((0 : ℤ).negOnePow : ℤ) •
        tateDeltaTo hA (0 + q) (0 + (q + 1)) (by omega) (tensorCup A S.X₃ 0 q a b)
    simpa only [Nat.cast_zero, neg_zero, Int.negOnePow_zero, Units.val_one, one_smul] using
      tensorCup_delta_second_zero S hS A hA q a b
  | succ p ih =>
    have hp : -((p + 1 : ℕ) : ℤ) + 1 = -(p : ℤ) := by omega
    let e := tensorFirstDownIso A S.X₁ (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (q + 1) hp
    apply e.toLinearEquiv.injective
    change tateDeltaTo (scalarSplit_tensorRight_shortExact _
        (shiftDownSequence_scalarSplitting A) S.X₁)
        (-((p + 1 : ℕ) : ℤ) + (q + 1)) (-(p : ℤ) + (q + 1)) _
        (tensorCup A S.X₁ (-((p + 1 : ℕ) : ℤ)) (q + 1) a (TateCohomology.δ hS q b)) =
      e.hom (((-((p + 1 : ℕ) : ℤ)).negOnePow : ℤ) • tateDeltaTo hA _ _ _
        (tensorCup A S.X₃ (-((p + 1 : ℕ) : ℤ)) q a b))
    rw [← tensorCup_delta_first_to (shiftDownSequence A) (shiftDownSequence_shortExact A) S.X₁
        (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) S.X₁)
        (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) (q + 1) hp,
      ih (shiftDown A) (shiftDownTensor_shortExact S A hA), map_zsmul]
    have hd := tensorDeltaTo_downLeft S A hA (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) q hp
    rw [tensorFirstDownIso_hom, tensorFirstDownIso_hom] at hd
    have ha := ConcreteCategory.congr_hom hd (tensorCup A S.X₃ (-((p + 1 : ℕ) : ℤ)) q a b)
    change e.hom (tateDeltaTo hA (-((p + 1 : ℕ) : ℤ) + q) (-((p + 1 : ℕ) : ℤ) + (q + 1)) _
        (tensorCup A S.X₃ (-((p + 1 : ℕ) : ℤ)) q a b)) =
      -(tateDeltaTo (shiftDownTensor_shortExact S A hA)
        (-(p : ℤ) + q) (-(p : ℤ) + (q + 1)) _
        (tateDeltaTo (scalarSplit_tensorRight_shortExact _
          (shiftDownSequence_scalarSplitting A) S.X₃) (-((p + 1 : ℕ) : ℤ) + q) (-(p : ℤ) + q) _
          (tensorCup A S.X₃ (-((p + 1 : ℕ) : ℤ)) q a b))) at ha
    rw [ha, ← tensorCup_delta_first_to (shiftDownSequence A) (shiftDownSequence_shortExact A) S.X₃
      (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) S.X₃)
      (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) q hp]
    have hs : ((-(p : ℤ)).negOnePow : ℤ) = -((-((p + 1 : ℕ) : ℤ)).negOnePow : ℤ) := by
      have h := congrArg Units.val (Int.negOnePow_succ (-((p + 1 : ℕ) : ℤ)))
      rw [hp] at h
      exact h
    rw [hs, neg_smul, smul_neg]

/-- The second-variable boundary law, with Serre's sign, in every integer bidegree. -/
lemma tensorCup_delta_second (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (A : Rep.{u} R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (p q : ℤ) (a : tateCohomology A p) (b : tateCohomology S.X₃ q) :
    tensorCup A S.X₁ p (q + 1) a (TateCohomology.δ hS q b) =
      (p.negOnePow : ℤ) • tateDeltaTo hA (p + q) (p + (q + 1)) (by omega)
        (tensorCup A S.X₃ p q a b) := by
  cases p with
  | ofNat p => exact tensorCup_delta_second_nonneg S hS A hA p q a b
  | negSucc p => exact tensorCup_delta_second_nonpos S hS A hA (p + 1) q a b

end Langlands.Tate
