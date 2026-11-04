import Langlands.AlgebraicGeometry.Deformation.ArtinianTests
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Artinian tests and elementary steps in their kernel filtration -/

noncomputable section

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.ArtinianTest

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]

/-- Equality of the actual algebra maps is equality of test arrows. -/
@[ext]
lemma hom_ext {A B : ArtinianTest k K} {q r : A ⟶ B}
    (h : toAlgHom q = toAlgHom r) : q = r := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact CommAlgCat.hom_ext h

/-- The augmentation on a quotient by an ideal killed by the original augmentation. -/
def quotientAugmentation (A : ArtinianTest k K) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom) : A.algebra ⧸ I →ₐ[k] K :=
  Ideal.Quotient.liftₐ I A.augmentation (fun _ hx ↦ RingHom.mem_ker.mp (hI hx))

lemma quotientAugmentation_surjective (A : ArtinianTest k K) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom) :
    Function.Surjective (quotientAugmentation A I hI) := by
  intro y
  obtain ⟨x, hx⟩ := A.augmentation_surjective y
  exact ⟨Ideal.Quotient.mk I x, hx⟩

/-- The quotient is again an actual augmented local Artinian test. -/
def quotient (A : ArtinianTest k K) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom) : ArtinianTest k K := by
  have : Nontrivial (A.algebra ⧸ I) :=
    (quotientAugmentation A I hI).toRingHom.domain_nontrivial
  have : IsLocalRing (A.algebra ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact mk (A.algebra ⧸ I) (quotientAugmentation A I hI)
    (quotientAugmentation_surjective A I hI)

/-- The genuine quotient algebra map, retaining its augmentation triangle. -/
def quotientMap (A : ArtinianTest k K) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom) : A ⟶ quotient A I hI :=
  homMk (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.liftₐ_comp I A.augmentation _)

@[simp]
lemma toAlgHom_quotientMap (A : ArtinianTest k K) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom) :
    toAlgHom (quotientMap A I hI) = Ideal.Quotient.mkₐ k I := rfl

lemma quotientMap_surjective (A : ArtinianTest k K) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom) :
    Function.Surjective (toAlgHom (quotientMap A I hI)) :=
  Ideal.Quotient.mkₐ_surjective k I

@[simp]
lemma ker_quotientMap (A : ArtinianTest k K) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom) :
    RingHom.ker (toAlgHom (quotientMap A I hI)).toRingHom = I :=
  Ideal.mk_ker

/-- An actual test arrow descends through every ideal in its kernel. -/
def quotientLift {A B : ArtinianTest k K} (q : A ⟶ B) (I : Ideal A.algebra)
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hIq : I ≤ RingHom.ker (toAlgHom q).toRingHom) : quotient A I hI ⟶ B :=
  homMk (Ideal.Quotient.liftₐ I (toAlgHom q)
    (fun _ hx ↦ RingHom.mem_ker.mp (hIq hx))) (by
      apply Ideal.Quotient.algHom_ext
      exact augmentation_comp q)

lemma quotientMap_lift {A B : ArtinianTest k K} (q : A ⟶ B)
    (I : Ideal A.algebra) (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hIq : I ≤ RingHom.ker (toAlgHom q).toRingHom) :
    quotientMap A I hI ≫ quotientLift q I hI hIq = q := by
  apply hom_ext
  exact Ideal.Quotient.liftₐ_comp I (toAlgHom q) _

lemma quotientLift_surjective {A B : ArtinianTest k K} (q : A ⟶ B)
    (I : Ideal A.algebra) (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hIq : I ≤ RingHom.ker (toAlgHom q).toRingHom)
    (hq : Function.Surjective (toAlgHom q)) :
    Function.Surjective (toAlgHom (quotientLift q I hI hIq)) := by
  intro y
  obtain ⟨x, hx⟩ := hq y
  exact ⟨Ideal.Quotient.mk I x, hx⟩

lemma quotientLift_injective {A B : ArtinianTest k K} (q : A ⟶ B)
    (I : Ideal A.algebra) (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hIq : I ≤ RingHom.ker (toAlgHom q).toRingHom)
    (hker : RingHom.ker (toAlgHom q).toRingHom = I) :
    Function.Injective (toAlgHom (quotientLift q I hI hIq)) :=
  (Ideal.injective_lift_iff (fun _ hx ↦ RingHom.mem_ker.mp (hIq hx))).mpr hker

/-- Bijective algebra maps are elementary in the chosen kernel-annihilation convention. -/
lemma isElementary_of_bijective {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Bijective (toAlgHom q)) : IsElementarySurjection q := by
  refine ⟨hq.2, ?_⟩
  rw [(RingHom.injective_iff_ker_eq_bot (toAlgHom q).toRingHom).mp hq.1, Ideal.mul_bot]

/-- The compatible quotient map for nested ideals. -/
def quotientFactor (A : ArtinianTest k K) {I J : Ideal A.algebra}
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hJ : J ≤ RingHom.ker A.augmentation.toRingHom) (hIJ : I ≤ J) :
    quotient A I hI ⟶ quotient A J hJ :=
  homMk (Ideal.Quotient.factorₐ k hIJ) (by
    apply Ideal.Quotient.algHom_ext
    rfl)

lemma quotientFactor_surjective (A : ArtinianTest k K) {I J : Ideal A.algebra}
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hJ : J ≤ RingHom.ker A.augmentation.toRingHom) (hIJ : I ≤ J) :
    Function.Surjective (toAlgHom (quotientFactor A hI hJ hIJ)) :=
  Ideal.Quotient.factor_surjective hIJ

lemma quotientMap_factor (A : ArtinianTest k K) {I J : Ideal A.algebra}
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hJ : J ≤ RingHom.ker A.augmentation.toRingHom) (hIJ : I ≤ J) :
    quotientMap A I hI ≫ quotientFactor A hI hJ hIJ = quotientMap A J hJ := by
  apply hom_ext
  rfl

lemma ker_quotientFactor (A : ArtinianTest k K) {I J : Ideal A.algebra}
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hJ : J ≤ RingHom.ker A.augmentation.toRingHom) (hIJ : I ≤ J) :
    RingHom.ker (toAlgHom (quotientFactor A hI hJ hIJ)).toRingHom =
      J.map (Ideal.Quotient.mk I) := by
  change RingHom.ker (Ideal.Quotient.factor hIJ) = _
  unfold Ideal.Quotient.factor
  rw [Ideal.ker_quotient_lift, Ideal.mk_ker]

/-- A quotient step is elementary when multiplication by the maximal ideal lands
in the smaller ideal. -/
lemma quotientFactor_isElementary (A : ArtinianTest k K) {I J : Ideal A.algebra}
    (hI : I ≤ RingHom.ker A.augmentation.toRingHom)
    (hJ : J ≤ RingHom.ker A.augmentation.toRingHom) (hIJ : I ≤ J)
    (hm : IsLocalRing.maximalIdeal A.algebra * J ≤ I) :
    IsElementarySurjection (quotientFactor A hI hJ hIJ) := by
  refine ⟨quotientFactor_surjective A hI hJ hIJ, ?_⟩
  rw [ker_quotientFactor]
  have : IsLocalRing (A.algebra ⧸ I) :=
    inferInstanceAs (IsLocalRing (quotient A I hI).algebra)
  change IsLocalRing.maximalIdeal (A.algebra ⧸ I) *
    J.map (Ideal.Quotient.mk I) = ⊥
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective, ← Ideal.map_mul]
  exact Ideal.map_mk_eq_bot_of_le hm

/-- The actual kernel filtration by powers of the source maximal ideal. -/
def kernelFiltration {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    Ideal A.algebra :=
  IsLocalRing.maximalIdeal A.algebra ^ n * RingHom.ker (toAlgHom q).toRingHom

@[simp]
lemma kernelFiltration_zero {A B : ArtinianTest k K} (q : A ⟶ B) :
    kernelFiltration q 0 = RingHom.ker (toAlgHom q).toRingHom := by
  simp [kernelFiltration]

lemma maximalIdeal_mul_kernelFiltration {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    IsLocalRing.maximalIdeal A.algebra * kernelFiltration q n =
      kernelFiltration q (n + 1) := by
  simp only [kernelFiltration, pow_succ', mul_assoc]

lemma kernelFiltration_succ_le {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    kernelFiltration q (n + 1) ≤ kernelFiltration q n := by
  rw [← maximalIdeal_mul_kernelFiltration]
  exact Ideal.mul_le_right

lemma kernelFiltration_le_ker {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    kernelFiltration q n ≤ RingHom.ker (toAlgHom q).toRingHom :=
  Ideal.mul_le_right

lemma kernelFiltration_le_augmentation {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    kernelFiltration q n ≤ RingHom.ker A.augmentation.toRingHom := by
  rw [ker_augmentation]
  exact Ideal.mul_le_right.trans (ker_le_maximalIdeal q)

/-- The filtration terminates, without a choice of coefficient field or a dimension bound. -/
lemma kernelFiltration_eventually_bot {A B : ArtinianTest k K} (q : A ⟶ B) :
    ∃ n : ℕ, kernelFiltration q n = ⊥ := by
  obtain ⟨n, hn⟩ := maximalIdeal_isNilpotent A
  use n
  simp [kernelFiltration, hn]

/-- The augmented test at a stage of the kernel filtration. -/
def filtrationTest {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) : ArtinianTest k K :=
  quotient A (kernelFiltration q n) (kernelFiltration_le_augmentation q n)

/-- The original algebra maps genuinely to each stage. -/
def filtrationMap {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) : A ⟶ filtrationTest q n :=
  quotientMap A (kernelFiltration q n) (kernelFiltration_le_augmentation q n)

/-- Consecutive stages give actual augmentation-preserving surjections. -/
def filtrationStep {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    filtrationTest q (n + 1) ⟶ filtrationTest q n :=
  quotientFactor A (kernelFiltration_le_augmentation q (n + 1))
    (kernelFiltration_le_augmentation q n) (kernelFiltration_succ_le q n)

lemma filtrationStep_isElementary {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    IsElementarySurjection (filtrationStep q n) :=
  quotientFactor_isElementary A _ _ _ (maximalIdeal_mul_kernelFiltration q n).le

lemma filtrationMap_step {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    filtrationMap q (n + 1) ≫ filtrationStep q n = filtrationMap q n :=
  quotientMap_factor A _ _ _

/-- The map from a kernel-filtration stage to the original target. -/
def filtrationLift {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    filtrationTest q n ⟶ B :=
  quotientLift q (kernelFiltration q n) (kernelFiltration_le_augmentation q n)
    (kernelFiltration_le_ker q n)

lemma filtrationMap_lift {A B : ArtinianTest k K} (q : A ⟶ B) (n : ℕ) :
    filtrationMap q n ≫ filtrationLift q n = q :=
  quotientMap_lift q _ _ _

lemma filtrationLift_zero_isElementary {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Surjective (toAlgHom q)) :
    IsElementarySurjection (filtrationLift q 0) :=
  isElementary_of_bijective _ ⟨quotientLift_injective q _ _ _
    (kernelFiltration_zero q).symm, quotientLift_surjective q _ _ _ hq⟩

lemma filtrationMap_isElementary_of_eq_bot {A B : ArtinianTest k K} (q : A ⟶ B)
    (n : ℕ) (hn : kernelFiltration q n = ⊥) :
    IsElementarySurjection (filtrationMap q n) := by
  refine ⟨quotientMap_surjective A _ _, ?_⟩
  change IsLocalRing.maximalIdeal A.algebra *
    RingHom.ker (toAlgHom (quotientMap A _ _)).toRingHom = ⊥
  rw [ker_quotientMap, hn, Ideal.mul_bot]

/-- A composition-closed property of all elementary surjections holds for every
surjection of actual augmented local Artinian tests. -/
lemma surjective_induction
    (P : ∀ {A B : ArtinianTest k K}, (A ⟶ B) → Prop)
    (hElementary : ∀ {A B : ArtinianTest k K} (q : A ⟶ B),
      IsElementarySurjection q → P q)
    (hComp : ∀ {A B C : ArtinianTest k K} (q : A ⟶ B) (r : B ⟶ C),
      P q → P r → P (q ≫ r))
    {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Surjective (toAlgHom q)) : P q := by
  have descend : ∀ n : ℕ, P (filtrationMap q n) → P (filtrationMap q 0) := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih =>
      intro hn
      apply ih
      simpa only [filtrationMap_step] using hComp (filtrationMap q (n + 1))
        (filtrationStep q n) hn (hElementary _ (filtrationStep_isElementary q n))
  obtain ⟨n, hn⟩ := kernelFiltration_eventually_bot q
  have hzero : P (filtrationMap q 0) :=
    descend n (hElementary _ (filtrationMap_isElementary_of_eq_bot q n hn))
  simpa only [filtrationMap_lift] using hComp (filtrationMap q 0)
    (filtrationLift q 0) hzero (hElementary _ (filtrationLift_zero_isElementary q hq))

end Langlands.AlgebraicGeometry.Deformation.ArtinianTest
