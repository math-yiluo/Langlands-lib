module

public import Langlands.RingTheory.WeilRestriction.PresentedAlgebra
public import Mathlib.RingTheory.Smooth.Basic
import Langlands.RingTheory.TensorProduct.QuotientKernel

/-! # Infinitesimal lifting for Weil restriction along a finite projective algebra -/

public section

open Algebra
open scoped TensorProduct

namespace Langlands.Algebra.WeilRestriction

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]

instance instFormallySmooth [FormallySmooth B C] : FormallySmooth A (WeilRestriction A B C) := by
  apply FormallySmooth.iff_comp_surjective.mpr
  intro T _ _ I square point
  let π := Ideal.Quotient.mkₐ A I
  let q := Algebra.TensorProduct.lTensor (S := B) B π
  have surj : Function.Surjective q :=
    LinearMap.lTensor_surjective B (Ideal.Quotient.mkₐ_surjective A I)
  have nil : IsNilpotent (RingHom.ker q) := by
    refine ⟨2, ?_⟩
    have ker_eq : RingHom.ker q = Ideal.rightTensorIdeal A B I :=
      Ideal.ker_tensorProduct_map_id_quotient (R := A) (A := B) I
    change RingHom.ker q ^ 2 = ⊥
    rw [ker_eq, Ideal.rightTensorIdeal_def, ← Ideal.map_pow, square, Ideal.map_bot]
  let p := homEquiv A B C _ point
  obtain ⟨up, hup⟩ : ∃ up : C →ₐ[B] B ⊗[A] T, q.comp up = p :=
    ⟨FormallySmooth.liftOfSurjective p q surj nil, FormallySmooth.comp_liftOfSurjective ..⟩
  use (homEquiv A B C T).symm up
  apply (homEquiv A B C _).injective
  rw [homEquiv_comp, Equiv.apply_symm_apply]
  exact hup

instance instSmooth [Smooth B C] : Smooth A (WeilRestriction A B C) :=
  ⟨inferInstance, inferInstance⟩

end Langlands.Algebra.WeilRestriction
