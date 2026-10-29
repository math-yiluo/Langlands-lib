import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Tactic.Ring

/-! # Cotangent functionals and augmented dual-number maps -/

universe u v w

namespace Langlands.AlgebraicGeometry

variable {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]

/-- Subtract the constant part of an augmented algebra element. -/
def augmentationDifference (r : A →ₐ[K] K) : A →ₗ[K] RingHom.ker r.toRingHom where
  toFun a := ⟨a - algebraMap K A (r a), by simp⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
    abel
  map_smul' c a := by
    apply Subtype.ext
    change c • a - algebraMap K A (r (c • a)) =
      c • (a - algebraMap K A (r a))
    simp [Algebra.smul_def, mul_sub]

@[simp]
lemma augmentationDifference_coe (r : A →ₐ[K] K) (a : A) :
    (augmentationDifference r a : A) = a - algebraMap K A (r a) := rfl

@[simp]
lemma augmentationDifference_algebraMap (r : A →ₐ[K] K) (c : K) :
    augmentationDifference r (algebraMap K A c) = 0 := by
  apply Subtype.ext
  change algebraMap K A c - algebraMap K A (r (algebraMap K A c)) = 0
  rw [r.commutes]
  exact sub_self _

@[simp]
lemma augmentationDifference_mem_ker (r : A →ₐ[K] K) (a : RingHom.ker r.toRingHom) :
    augmentationDifference r a = a := by
  apply Subtype.ext
  simp only [augmentationDifference_coe]
  have ha : r a = 0 := a.property
  simp [ha]

/-- The cotangent class of an element after subtracting its constant part. -/
def augmentationCotangent (r : A →ₐ[K] K) :
    A →ₗ[K] (RingHom.ker r.toRingHom).Cotangent :=
  ((RingHom.ker r.toRingHom).toCotangent.restrictScalars K).comp
    (augmentationDifference r)

@[simp]
lemma augmentationCotangent_apply (r : A →ₐ[K] K) (a : A) :
    augmentationCotangent r a =
      (RingHom.ker r.toRingHom).toCotangent (augmentationDifference r a) := rfl

@[simp]
lemma augmentationCotangent_algebraMap (r : A →ₐ[K] K) (c : K) :
    augmentationCotangent r (algebraMap K A c) = 0 := by
  rw [augmentationCotangent_apply, augmentationDifference_algebraMap, map_zero]

@[simp]
lemma augmentationCotangent_mem_ker (r : A →ₐ[K] K) (a : RingHom.ker r.toRingHom) :
    augmentationCotangent r a = (RingHom.ker r.toRingHom).toCotangent a := by
  rw [augmentationCotangent_apply, augmentationDifference_mem_ker]

lemma augmentationCotangent_mul (r : A →ₐ[K] K) (a b : A) :
    augmentationCotangent r (a * b) =
      r a • augmentationCotangent r b + r b • augmentationCotangent r a := by
  let I := RingHom.ker r.toRingHom
  change I.toCotangent (augmentationDifference r (a * b)) =
    ((I.toCotangent.restrictScalars K) (r a • augmentationDifference r b)) +
    ((I.toCotangent.restrictScalars K) (r b • augmentationDifference r a))
  rw [← map_add]
  apply I.toCotangent_eq.mpr
  have hprod : ((augmentationDifference r a : A) * (augmentationDifference r b : A))
      ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (augmentationDifference r a).property
      (augmentationDifference r b).property
  convert hprod using 1
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower,
    augmentationDifference_coe, map_mul, Algebra.smul_def]
  ring

/-- A cotangent functional gives an augmented algebra map to the dual numbers. -/
def cotangentDualNumberLift (r : A →ₐ[K] K)
    (ell : (RingHom.ker r.toRingHom).Cotangent →ₗ[K] K) :
    A →ₐ[K] DualNumber K where
  toFun a := (r a, ell (augmentationCotangent r a))
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change ell (augmentationCotangent r 1) = 0
      have h : augmentationCotangent r 1 = 0 := by
        simpa using augmentationCotangent_algebraMap r (1 : K)
      rw [h, map_zero]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul r a b
    · change ell (augmentationCotangent r (a * b)) =
        r a * ell (augmentationCotangent r b) + ell (augmentationCotangent r a) * r b
      rw [augmentationCotangent_mul, map_add, map_smul, map_smul]
      simp only [smul_eq_mul, mul_comm]
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero r
    · change ell (augmentationCotangent r 0) = 0
      rw [map_zero, map_zero]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · exact map_add r a b
    · change ell (augmentationCotangent r (a + b)) =
        ell (augmentationCotangent r a) + ell (augmentationCotangent r b)
      rw [map_add, map_add]
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact r.commutes c
    · change ell (augmentationCotangent r (algebraMap K A c)) = 0
      rw [augmentationCotangent_algebraMap, map_zero]

@[simp]
lemma cotangentDualNumberLift_fst (r : A →ₐ[K] K)
    (ell : (RingHom.ker r.toRingHom).Cotangent →ₗ[K] K) (a : A) :
    (cotangentDualNumberLift r ell a).fst = r a := rfl

@[simp]
lemma cotangentDualNumberLift_snd (r : A →ₐ[K] K)
    (ell : (RingHom.ker r.toRingHom).Cotangent →ₗ[K] K) (a : A) :
    (cotangentDualNumberLift r ell a).snd = ell (augmentationCotangent r a) := rfl

@[simp]
lemma cotangentDualNumberLift_projection (r : A →ₐ[K] K)
    (ell : (RingHom.ker r.toRingHom).Cotangent →ₗ[K] K) :
    (TrivSqZeroExt.fstHom K K K).comp (cotangentDualNumberLift r ell) = r := by
  ext
  rfl

lemma cotangentDualNumberLift_eq_constant_iff (r : A →ₐ[K] K)
    (ell : (RingHom.ker r.toRingHom).Cotangent →ₗ[K] K) :
    cotangentDualNumberLift r ell = (TrivSqZeroExt.inlAlgHom K K K).comp r ↔ ell = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro c
    obtain ⟨a, rfl⟩ := (RingHom.ker r.toRingHom).toCotangent_surjective c
    have ha := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun h (a : A))
    change ell (augmentationCotangent r (a : A)) = 0 at ha
    rw [augmentationCotangent_mem_ker] at ha
    exact ha
  · rintro rfl
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext <;> rfl

variable {B : Type w} [CommRing B] [Algebra K B]

/-- The cotangent map induced by a homomorphism of augmented algebras. -/
def augmentationCotangentMap (r : A →ₐ[K] K) (f : B →ₐ[K] A) :
    (RingHom.ker (r.comp f).toRingHom).Cotangent →ₗ[K]
      (RingHom.ker r.toRingHom).Cotangent :=
  Ideal.mapCotangent _ _ f (by intro b hb; exact hb)

lemma augmentationCotangentMap_apply (r : A →ₐ[K] K) (f : B →ₐ[K] A) (b : B) :
    augmentationCotangentMap r f (augmentationCotangent (r.comp f) b) =
      augmentationCotangent r (f b) := by
  change (RingHom.ker r.toRingHom).toCotangent
    ⟨f (b - algebraMap K B ((r.comp f) b)), _⟩ =
      (RingHom.ker r.toRingHom).toCotangent
        (augmentationDifference r (f b))
  congr 1
  apply Subtype.ext
  change f (b - algebraMap K B ((r.comp f) b)) =
    f b - algebraMap K A (r (f b))
  rw [map_sub, f.commutes]
  rfl

lemma cotangentDualNumberLift_comp (r : A →ₐ[K] K)
    (ell : (RingHom.ker r.toRingHom).Cotangent →ₗ[K] K) (f : B →ₐ[K] A) :
    (cotangentDualNumberLift r ell).comp f =
      cotangentDualNumberLift (r.comp f) (ell.comp (augmentationCotangentMap r f)) := by
  apply AlgHom.ext
  intro b
  apply TrivSqZeroExt.ext
  · rfl
  · change ell (augmentationCotangent r (f b)) =
      ell (augmentationCotangentMap r f (augmentationCotangent (r.comp f) b))
    rw [augmentationCotangentMap_apply]

lemma cotangentDualNumberLift_comp_eq_constant_iff (r : A →ₐ[K] K)
    (ell : (RingHom.ker r.toRingHom).Cotangent →ₗ[K] K) (f : B →ₐ[K] A) :
    (cotangentDualNumberLift r ell).comp f =
      (TrivSqZeroExt.inlAlgHom K K K).comp (r.comp f) ↔
      ell.comp (augmentationCotangentMap r f) = 0 := by
  rw [cotangentDualNumberLift_comp, cotangentDualNumberLift_eq_constant_iff]

end Langlands.AlgebraicGeometry
