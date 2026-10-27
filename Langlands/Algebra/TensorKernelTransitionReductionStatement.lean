import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Tensor-kernel transition reduction for Stacks 00MO -/

universe u₁ u₂ u₃ u₄ u₅ u₆

open scoped TensorProduct

namespace Langlands.Algebra

/-- The reduction step in the proof of Stacks Project Lemma 10.99.14 (tag 00MO): its
hypotheses, with the Tor transition written through ideal tensor kernels, give the two
hypotheses of Lemma 10.99.10 (tag 00ML) for `R'`, `I R'` and `M'`. -/
def TensorKernelTransitionReductionStatement : Prop :=
  ∀ (R : Type u₁) (R' : Type u₂) (S : Type u₃) (S' : Type u₄)
    (M : Type u₅) (M' : Type u₆)
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R R'] [Algebra R S] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup M'] [Module R' M'] [Module S M'] [Module S' M']
    [IsScalarTower R' S' M'] [IsScalarTower S S' M']
    (I : Ideal R) (W : Submonoid (S ⊗[R] R')) (f : M →ₗ[S] M'),
    I.FG →
    (letI : Algebra (S ⊗[R] R') S' :=
      (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R S S')
        (IsScalarTower.toAlgHom R R' S')).toRingHom.toAlgebra
     IsLocalization W S') →
    IsBaseChange S' f →
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) →
    (∀ (n : ℕ) (a : Fin n → I) (m : Fin n → M), ∑ k, (a k : R) • m k = 0 →
      ∑ k, (⟨algebraMap R R' (a k), Ideal.mem_map_of_mem _ (a k).2⟩ :
          I.map (algebraMap R R')) ⊗ₜ[R'] f (m k) = 0) →
    Function.Injective (LinearMap.rTensor M' (I.map (algebraMap R R')).subtype) ∧
      Module.Flat (R' ⧸ I.map (algebraMap R R'))
        ((R' ⧸ I.map (algebraMap R R')) ⊗[R'] M')

end Langlands.Algebra
