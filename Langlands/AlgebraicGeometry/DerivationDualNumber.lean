import Langlands.GroupScheme.GeneralLinearDualNumber
import Mathlib.RingTheory.Derivation.Basic

/-! # Derivations and augmented dual-number algebra maps -/

universe u v

noncomputable section

namespace Langlands.AlgebraicGeometry

open Langlands.GroupScheme.GeneralLinear.DualNumber

variable {K : Type u} {A : Type v} [CommRing K] [CommRing A] [Algebra K A]

/-- A derivation with coefficient action through an augmentation gives the
algebra map with that constant coefficient and the derivation as epsilon coefficient. -/
def derivationDualNumberLift (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    Derivation K A K → A →ₐ[K] DualNumber K := by
  let := r.toRingHom.toAlgebra
  intro D
  exact
    { toFun := fun a ↦ (r a, D a)
      map_one' := TrivSqZeroExt.ext (map_one r) D.map_one_eq_zero
      map_zero' := TrivSqZeroExt.ext (map_zero r) (map_zero D)
      map_add' := fun a b ↦ TrivSqZeroExt.ext (map_add r a b) (map_add D a b)
      map_mul' := fun a b ↦ TrivSqZeroExt.ext (map_mul r a b) (by
        change D (a * b) = r a * D b + D a * r b
        have h := D.leibniz a b
        change D (a * b) = r a * D b + r b * D a at h
        rw [h, mul_comm (r b) (D a)])
      commutes' := fun c ↦ TrivSqZeroExt.ext (r.commutes c) (D.map_algebraMap c) }

@[simp]
lemma derivationDualNumberLift_fst (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    ∀ (D : Derivation K A K) (a : A), (derivationDualNumberLift r D a).fst = r a := by
  let := r.toRingHom.toAlgebra
  intros
  rfl

@[simp]
lemma derivationDualNumberLift_snd (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    ∀ (D : Derivation K A K) (a : A), (derivationDualNumberLift r D a).snd = D a := by
  let := r.toRingHom.toAlgebra
  intros
  rfl

@[simp]
lemma derivationDualNumberLift_projection (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    ∀ D, (TrivSqZeroExt.fstHom K K K).comp (derivationDualNumberLift r D) = r := by
  let := r.toRingHom.toAlgebra
  intro D
  exact AlgHom.ext fun _ ↦ rfl

/-- The epsilon coefficient of an augmented dual-number algebra map is a
derivation for the coefficient action through its augmentation. -/
def dualNumberAugmentedDerivation (r : A →ₐ[K] K)
    (f : {f : A →ₐ[K] DualNumber K // (TrivSqZeroExt.fstHom K K K).comp f = r}) :
    letI := r.toRingHom.toAlgebra
    Derivation K A K := by
  let := r.toRingHom.toAlgebra
  have hf (a : A) : (f.val a).fst = r a :=
    AlgHom.congr_fun f.property a
  exact
    { toFun := fun a ↦ (f.val a).snd
      map_add' := fun a b ↦ by
        simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c a ↦ by
        simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        change (f.val (a * b)).snd =
          r a * (f.val b).snd + r b * (f.val a).snd
        rw [map_mul]
        change (f.val a).fst * (f.val b).snd + (f.val a).snd * (f.val b).fst = _
        rw [hf, hf]
        rw [mul_comm (f.val a).snd] }

@[simp]
lemma dualNumberAugmentedDerivation_apply (r : A →ₐ[K] K)
    (f : {f : A →ₐ[K] DualNumber K // (TrivSqZeroExt.fstHom K K K).comp f = r})
    (a : A) : dualNumberAugmentedDerivation r f a = (f.val a).snd := rfl

/-- Derivations with action through an augmentation are precisely its algebra
lifts to the actual dual-number ring. -/
def derivationDualNumberEquiv (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    Derivation K A K ≃
      {f : A →ₐ[K] DualNumber K // (TrivSqZeroExt.fstHom K K K).comp f = r} := by
  let := r.toRingHom.toAlgebra
  exact
    { toFun := fun D ↦ ⟨derivationDualNumberLift r D, derivationDualNumberLift_projection r D⟩
      invFun := dualNumberAugmentedDerivation r
      left_inv := fun D ↦ Derivation.ext fun _ ↦ rfl
      right_inv := fun f ↦ by
        apply Subtype.ext
        apply AlgHom.ext
        intro a
        apply TrivSqZeroExt.ext
        · exact (AlgHom.congr_fun f.property a).symm
        · rfl }

@[simp]
lemma derivationDualNumberEquiv_apply_val (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    ∀ D, (derivationDualNumberEquiv r D).val = derivationDualNumberLift r D := by
  let := r.toRingHom.toAlgebra
  intros
  rfl

/-- Addition of derivations adds the epsilon coefficients while fixing the augmentation. -/
lemma derivationDualNumberLift_add_snd (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    ∀ (D E : Derivation K A K) (a : A),
      (derivationDualNumberLift r (D + E) a).snd =
        (derivationDualNumberLift r D a).snd + (derivationDualNumberLift r E a).snd := by
  let := r.toRingHom.toAlgebra
  intros
  rfl

/-- Scalar multiplication of derivations is the actual epsilon-scaling algebra map. -/
lemma derivationDualNumberLift_smul (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    ∀ (c : K) (D : Derivation K A K),
      derivationDualNumberLift r (c • D) =
        (epsilonScale c).comp (derivationDualNumberLift r D) := by
  let := r.toRingHom.toAlgebra
  intro c D
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · simp
  · simp [Derivation.smul_apply]

/-- Zero derivation gives the constant algebra lift of the augmentation. -/
lemma derivationDualNumberLift_zero (r : A →ₐ[K] K) :
    letI := r.toRingHom.toAlgebra
    derivationDualNumberLift r 0 = (TrivSqZeroExt.inlAlgHom K K K).comp r := by
  let := r.toRingHom.toAlgebra
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext <;> rfl

end Langlands.AlgebraicGeometry
