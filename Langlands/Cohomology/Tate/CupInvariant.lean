import Langlands.Cohomology.Tate.CupProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- Tensoring with an invariant vector is an actual equivariant coefficient map. -/
def tensorInvariantRight (A B : Rep.{u} R G) (b : B.ρ.invariants) : A ⟶ A ⊗ B :=
  Rep.ofHom ⟨(TensorProduct.mk R A B).flip b, fun g => by
    ext a
    change (A.ρ g a) ⊗ₜ[R] (b : B) = (A.ρ g a) ⊗ₜ[R] (B.ρ g b)
    rw [b.property g]⟩

lemma tensorInvariantRight_naturality {A A' : Rep.{u} R G}
    (f : A ⟶ A') (B : Rep.{u} R G) (b : B.ρ.invariants) :
    f ≫ tensorInvariantRight A' B b =
      tensorInvariantRight A B b ≫ (f ⊗ₘ 𝟙 B) := by
  ext a
  rfl

/-- The maps given by a fixed invariant vector form a map of coefficient sequences. -/
def tensorInvariantSequence (S : ShortComplex (Rep.{u} R G))
    (B : Rep.{u} R G) (b : B.ρ.invariants) :
    S ⟶ S.map (MonoidalCategory.tensorRight B) where
  τ₁ := tensorInvariantRight S.X₁ B b
  τ₂ := tensorInvariantRight S.X₂ B b
  τ₃ := tensorInvariantRight S.X₃ B b
  comm₁₂ := (tensorInvariantRight_naturality S.f B b).symm
  comm₂₃ := (tensorInvariantRight_naturality S.g B b).symm

variable [Fintype G]

lemma tensorInvariant_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (B : Rep.{u} R G) (hT : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (b : B.ρ.invariants) (n : ℤ) :
    TateCohomology.δ hS n ≫
        (tateCohomologyFunctor (n + 1)).map (tensorInvariantRight S.X₁ B b) =
      (tateCohomologyFunctor n).map (tensorInvariantRight S.X₃ B b) ≫
        TateCohomology.δ hT n :=
  TateCohomology.δ_naturality hS hT (tensorInvariantSequence S B b) n

lemma tensorInvariant_downNegative (A B : Rep.{u} R G) (b : B.ρ.invariants) (n : ℕ) :
    (shiftDownNegativeIso A n).hom ≫
        (tateCohomologyFunctor (-(n : ℤ))).map (tensorInvariantRight (shiftDown A) B b) =
      (tateCohomologyFunctor (-(n + 1 : ℤ))).map (tensorInvariantRight A B b) ≫
        (tensorShiftDownLeftNegativeIso A B n).hom := by
  have h := tensorInvariant_delta (shiftDownSequence A) (shiftDownSequence_shortExact A) B
    (scalarSplit_tensorRight_shortExact _ (shiftDownSequence_scalarSplitting A) B)
    b (-(n + 1 : ℤ))
  have hn : -(n + 1 : ℤ) + 1 = -(n : ℤ) := by omega
  change (shiftDownIso A (-(n + 1 : ℤ))).hom ≫
      (tateCohomologyFunctor (-(n + 1 : ℤ) + 1)).map
        (tensorInvariantRight (shiftDown A) B b) =
    (tateCohomologyFunctor (-(n + 1 : ℤ))).map (tensorInvariantRight A B b) ≫
      (tensorShiftDownLeftIso A B (-(n + 1 : ℤ))).hom at h
  change ((shiftDownIso A (-(n + 1 : ℤ))).hom ≫
      (tateDegreeIso (shiftDown A) hn).hom) ≫
      (tateCohomologyFunctor (-(n : ℤ))).map (tensorInvariantRight (shiftDown A) B b) =
    (tateCohomologyFunctor (-(n + 1 : ℤ))).map (tensorInvariantRight A B b) ≫
      ((tensorShiftDownLeftIso A B (-(n + 1 : ℤ))).hom ≫
        (tateDegreeIso (shiftDown A ⊗ B) hn).hom)
  rw [Category.assoc, tateDegreeIso_naturality (tensorInvariantRight (shiftDown A) B b) hn,
    ← Category.assoc, h, Category.assoc]

lemma tensorCupFirstNonneg_invariant (p : ℕ) (A B : Rep.{u} R G)
    (x : tateCohomology A p) (b : B.ρ.invariants) :
    tensorCupFirstNonneg p A B x (zeroClass B b) =
      (tateCohomologyFunctor p).map (tensorInvariantRight A B b) x := by
  induction p generalizing A with
  | zero =>
    obtain ⟨a, rfl⟩ := zeroClass_surjective A x
    change cupZero (tensorPairing A B) (zeroClass A a) (zeroClass B b) =
      (tateCohomologyFunctor 0).map (tensorInvariantRight A B b) (zeroClass A a)
    rw [cupZero_zeroClass]
    exact (zeroClass_naturality (tensorInvariantRight A B b) a).symm
  | succ p ih =>
    obtain ⟨a, rfl⟩ := (shiftUpIso A p).toLinearEquiv.surjective x
    change tensorCupFirstNonneg (p + 1) A B ((shiftUpIso A p).hom a) (zeroClass B b) =
      (tateCohomologyFunctor (p + 1)).map (tensorInvariantRight A B b) ((shiftUpIso A p).hom a)
    rw [tensorCupFirstNonneg_shift, ih]
    exact (ConcreteCategory.congr_hom
      (tensorInvariant_delta (shiftUpSequence A) (shiftUpSequence_shortExact A) B
        (scalarSplit_tensorRight_shortExact _ (shiftUpSequence_scalarSplitting A) B) b p) a).symm

lemma tensorCupFirstNonpos_invariant (p : ℕ) (A B : Rep.{u} R G)
    (x : tateCohomology A (-(p : ℤ))) (b : B.ρ.invariants) :
    tensorCupFirstNonpos p A B x (zeroClass B b) =
      (tateCohomologyFunctor (-(p : ℤ))).map (tensorInvariantRight A B b) x := by
  induction p generalizing A with
  | zero => exact tensorCupFirstNonneg_invariant 0 A B x b
  | succ p ih =>
    apply (tensorShiftDownLeftNegativeIso A B p).toLinearEquiv.injective
    change (tensorShiftDownLeftNegativeIso A B p).hom
        (tensorCupFirstNonpos (p + 1) A B x (zeroClass B b)) = _
    rw [tensorCupFirstNonpos_shift, ih]
    exact ConcreteCategory.congr_hom (tensorInvariant_downNegative A B b p) x

/-- In every degree, multiplication by a degree-zero invariant is its actual coefficient map. -/
lemma tensorCupFirst_invariant (p : ℤ) (A B : Rep.{u} R G)
    (x : tateCohomology A p) (b : B.ρ.invariants) :
    tensorCupFirst A B p x (zeroClass B b) =
      (tateCohomologyFunctor p).map (tensorInvariantRight A B b) x := by
  cases p with
  | ofNat p => exact tensorCupFirstNonneg_invariant p A B x b
  | negSucc p => exact tensorCupFirstNonpos_invariant (p + 1) A B x b

/-- The first boundary law with second degree zero needs tensor exactness, not a scalar splitting. -/
lemma tensorCupFirst_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (B : Rep.{u} R G) (hT : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
    (p : ℤ) (x : tateCohomology S.X₃ p) (b : tateCohomology B 0) :
    tensorCupFirst S.X₁ B (p + 1) (TateCohomology.δ hS p x) b =
      TateCohomology.δ hT p (tensorCupFirst S.X₃ B p x b) := by
  obtain ⟨b, rfl⟩ := zeroClass_surjective B b
  rw [tensorCupFirst_invariant, tensorCupFirst_invariant]
  exact ConcreteCategory.congr_hom (tensorInvariant_delta S hS B hT b p) x

end Langlands.Tate
