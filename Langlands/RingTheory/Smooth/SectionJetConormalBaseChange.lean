import Langlands.RingTheory.Smooth.SectionJetConormal
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Arbitrary scalar extension of section conormals -/

noncomputable section

open scoped TensorProduct
open TensorProduct

namespace Algebra.SectionJet

open Langlands.GroupScheme.CoordinateWeights

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (ε : A →ₐ[R] R) (B : Type*) [CommRing B] [Algebra R B]

private theorem firstSplitEquiv_mk_of_zero (a : A) (ha : ε a = 0) :
    firstSplitEquiv ε (Ideal.Quotient.mk _ a) =
      (0, (RingHom.ker ε).toCotangent ⟨a, ha⟩) := by
  apply (firstSplitEquiv ε).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = algebraMap R _ 0 +
    (cotangentEquivLayer ε ((RingHom.ker ε).toCotangent ⟨a, ha⟩)).val
  simp only [map_zero, zero_add]
  rfl

private theorem firstSplitEquiv_algebraMap (r : R) :
    firstSplitEquiv ε (algebraMap R _ r) = (r, 0) := by
  apply (firstSplitEquiv ε).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = algebraMap R _ r + (cotangentEquivLayer ε 0).val
  rw [map_zero, Submodule.coe_zero, add_zero]

private def firstSplitTensorEquiv :
    B ⊗[R] Quotient ε 1 ≃ₗ[B] B × (B ⊗[R] (RingHom.ker ε).Cotangent) :=
  AlgebraTensorModule.congr (.refl B B) (firstSplitEquiv ε) ≪≫ₗ
    prodRight R B B R (RingHom.ker ε).Cotangent ≪≫ₗ
    (AlgebraTensorModule.rid R B B).prodCongr (.refl B _)

private theorem firstSplitTensorEquiv_tmul (b : B) (x : Quotient ε 1) :
    firstSplitTensorEquiv ε B (b ⊗ₜ[R] x) =
      ((firstSplitEquiv ε x).1 • b, b ⊗ₜ[R] (firstSplitEquiv ε x).2) := by
  simp [firstSplitTensorEquiv]

private def firstSplitComparison :
    (B × (B ⊗[R] (RingHom.ker ε).Cotangent)) ≃ₗ[B]
      (B × (RingHom.ker (baseChangeAugmentation ε B)).Cotangent) :=
  (firstSplitTensorEquiv ε B).symm ≪≫ₗ (baseChangeEquiv ε B 1).toLinearEquiv ≪≫ₗ
    firstSplitEquiv (baseChangeAugmentation ε B)

private theorem firstSplitComparison_tmul (b : B) (a : A) (ha : ε a = 0) :
    firstSplitComparison ε B (0, b ⊗ₜ[R] (RingHom.ker ε).toCotangent ⟨a, ha⟩) =
      (0, (RingHom.ker (baseChangeAugmentation ε B)).toCotangent
        ⟨b ⊗ₜ[R] a, by simp [ha]⟩) := by
  have h := firstSplitTensorEquiv_tmul ε B b (Ideal.Quotient.mk _ a)
  rw [firstSplitEquiv_mk_of_zero ε a ha] at h
  simp only [zero_smul] at h
  rw [← h]
  simp only [firstSplitComparison, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    AlgEquiv.toLinearEquiv_apply, baseChangeEquiv_tmul_mk]
  exact firstSplitEquiv_mk_of_zero (baseChangeAugmentation ε B) _ (by simp [ha])

private theorem firstSplitComparison_scalar (b : B) :
    firstSplitComparison ε B (b, 0) = (b, 0) := by
  have h := firstSplitTensorEquiv_tmul ε B b (1 : Quotient ε 1)
  rw [show (1 : Quotient ε 1) = algebraMap R (Quotient ε 1) 1 from (map_one _).symm,
    firstSplitEquiv_algebraMap] at h
  simp only [one_smul, tmul_zero] at h
  rw [← h]
  simp only [firstSplitComparison, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    AlgEquiv.toLinearEquiv_apply]
  rw [show algebraMap R (Quotient ε 1) 1 = Ideal.Quotient.mk _ (1 : A) by simp,
    baseChangeEquiv_tmul_mk]
  have hb : algebraMap B (Quotient (baseChangeAugmentation ε B) 1) b =
      Ideal.Quotient.mk _ (b ⊗ₜ[R] (1 : A)) := rfl
  rw [← hb, firstSplitEquiv_algebraMap]

private theorem firstSplitComparison_fst (x : B ⊗[R] (RingHom.ker ε).Cotangent) :
    (firstSplitComparison ε B (0, x)).1 = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := (RingHom.ker ε).toCotangent_surjective x
    rw [firstSplitComparison_tmul ε B b a ha]
  | add x y hx hy =>
    have hxy : ((0 : B), x + y) = (0, x) + (0, y) := by simp
    rw [hxy, map_add, Prod.fst_add, hx, hy, add_zero]

/-- The linear comparison from the tensor of the augmentation conormal to the
conormal of the base-changed section. -/
def baseChangeConormalMap :
    B ⊗[R] (RingHom.ker ε).Cotangent →ₗ[B]
      (RingHom.ker (baseChangeAugmentation ε B)).Cotangent :=
  (LinearMap.snd B _ _).comp <|
    (firstSplitComparison ε B).toLinearMap.comp (LinearMap.inr B _ _)

/-- Arbitrary scalar extension commutes with the conormal module of a section. -/
def baseChangeConormalEquiv :
    B ⊗[R] (RingHom.ker ε).Cotangent ≃ₗ[B]
      (RingHom.ker (baseChangeAugmentation ε B)).Cotangent :=
  LinearEquiv.ofBijective (baseChangeConormalMap ε B) (by
    have h : ⇑(firstSplitComparison ε B) = Prod.map _root_.id (baseChangeConormalMap ε B) := by
      funext p
      obtain ⟨b, x⟩ := p
      have hbx : (b, x) = (b, 0) + (0, x) := by simp
      calc
        firstSplitComparison ε B (b, x) = firstSplitComparison ε B ((b, 0) + (0, x)) :=
          congrArg (firstSplitComparison ε B) hbx
        _ = (b, 0) + firstSplitComparison ε B (0, x) := by
          rw [map_add, firstSplitComparison_scalar]
        _ = Prod.map _root_.id (baseChangeConormalMap ε B) (b, x) := by
          apply Prod.ext
          · change b + (firstSplitComparison ε B (0, x)).1 = b
            rw [firstSplitComparison_fst, add_zero]
          · change 0 + (firstSplitComparison ε B (0, x)).2 = _
            rw [zero_add]
            rfl
    have hb := (firstSplitComparison ε B).bijective
    rw [h, Prod.map_bijective] at hb
    exact hb.2)

@[simp] theorem baseChangeConormalEquiv_tmul_classMap (b : B) (a : A) (ha : ε a = 0) :
    baseChangeConormalEquiv ε B (b ⊗ₜ[R] AugmentedAlgebra.classMap ε a) =
      AugmentedAlgebra.classMap (baseChangeAugmentation ε B) (b ⊗ₜ[R] a) := by
  have ht : baseChangeAugmentation ε B (b ⊗ₜ[R] a) = 0 := by simp [ha]
  rw [AugmentedAlgebra.classMap_ideal ε ⟨a, ha⟩,
    AugmentedAlgebra.classMap_ideal (baseChangeAugmentation ε B) ⟨b ⊗ₜ[R] a, ht⟩]
  exact congrArg Prod.snd (firstSplitComparison_tmul ε B b a ha)

end Algebra.SectionJet
