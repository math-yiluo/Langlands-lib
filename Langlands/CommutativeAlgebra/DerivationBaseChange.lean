import Langlands.CommutativeAlgebra.SemisimpleDerivation
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Etale.Descent

/-! # Scalar extension of derivations and their image-ideal quotients -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra.SemisimpleDerivation

section BaseChange

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  (S : Type w) [CommRing S] [Algebra R S] (D : Derivation R A A)

/-- Scalar extension of an algebra derivation, acting trivially on the new base. -/
def baseChange : Derivation S (S ⊗[R] A) (S ⊗[R] A) :=
  Derivation.mk' (D.toLinearMap.baseChange S) (by
    intro x y
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      induction y using TensorProduct.inductionOn with
      | tmul t b =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
          Derivation.coeFn_coe, Derivation.leibniz, TensorProduct.tmul_add, smul_eq_mul,
          Algebra.TensorProduct.tmul_mul_tmul]
        rw [mul_comm t s]
      | add y z hy hz =>
        simp only [mul_add, map_add, hy, hz, smul_eq_mul, mul_add, add_mul]
        abel
    | add x y hx hy =>
      simp only [add_mul, map_add, hx, hy, smul_eq_mul, mul_add, add_mul]
      abel)

@[simp] theorem baseChange_tmul (s : S) (a : A) :
    baseChange S D (s ⊗ₜ[R] a) = s ⊗ₜ[R] D a :=
  rfl

/-- Extending the image ideal agrees with taking the image ideal after extending
the derivation. -/
theorem span_range_baseChange :
    Ideal.span (Set.range (baseChange S D)) =
      (Ideal.span (Set.range D)).map
        (Algebra.TensorProduct.includeRight (A := S) (R := R)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul s a =>
      rw [baseChange_tmul]
      have h : (1 : S) ⊗ₜ[R] D a ∈
          (Ideal.span (Set.range D)).map
            (Algebra.TensorProduct.includeRight (A := S) (R := R)) :=
        Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, rfl⟩)
      simpa using Ideal.mul_mem_left _ (s ⊗ₜ[R] (1 : A)) h
    | add x y hx hy =>
      rw [map_add]
      exact Ideal.add_mem _ hx hy
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change (1 : S) ⊗ₜ[R] D a ∈ Ideal.span (Set.range (baseChange S D))
    exact Ideal.subset_span ⟨(1 : S) ⊗ₜ[R] a, rfl⟩

/-- Quotienting by the image ideal commutes with scalar extension. -/
def quotientBaseChangeEquiv :
    S ⊗[R] (A ⧸ Ideal.span (Set.range D)) ≃ₐ[S]
      (S ⊗[R] A) ⧸ Ideal.span (Set.range (baseChange S D)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S A S
    (Ideal.span (Set.range D))).trans
    (Ideal.quotientEquivAlgOfEq S (span_range_baseChange S D).symm)

end BaseChange

section Smoothness

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
  (K : Type w) [Field K] [Algebra k K]
  (D : Derivation k A A)

/-- Field specialization of the image-ideal comparison. -/
theorem imageIdeal_baseChange :
    imageIdeal (baseChange K D) =
      (imageIdeal D).map (Algebra.TensorProduct.includeRight (A := K) (R := k)) :=
  span_range_baseChange K D

variable [Module.FaithfullyFlat k K]

/-- An eigenvector decomposition after a faithfully flat field extension
suffices for smoothness of the original image-ideal quotient. -/
theorem smooth_quotient_imageIdeal_of_eigenBaseChange [Algebra.Smooth k A]
    (hD : HasEigenDecomposition (baseChange K D).toLinearMap) :
    Algebra.Smooth k (A ⧸ imageIdeal D) := by
  have : Algebra.Smooth K ((K ⊗[k] A) ⧸ Ideal.span (Set.range (baseChange K D))) :=
    smooth_quotient_imageIdeal (baseChange K D) hD
  have : Algebra.Smooth K (K ⊗[k] (A ⧸ imageIdeal D)) :=
    Algebra.Smooth.of_equiv (quotientBaseChangeEquiv K D).symm
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K

/-- Over an algebraically closed extension, local semisimplicity supplies the
eigenvector decomposition required for smooth descent. -/
theorem smooth_quotient_imageIdeal_of_locallySemisimple_baseChange
    [IsAlgClosed K] [Algebra.Smooth k A]
    (hD : LocallySemisimple (baseChange K D).toLinearMap) :
    Algebra.Smooth k (A ⧸ imageIdeal D) :=
  smooth_quotient_imageIdeal_of_eigenBaseChange K D hD.hasEigenDecomposition

end Smoothness

end Langlands.Algebra.SemisimpleDerivation
