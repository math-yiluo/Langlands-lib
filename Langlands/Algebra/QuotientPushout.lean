import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IsTensorProduct

universe u v w x

open scoped TensorProduct

namespace Langlands.Algebra

attribute [local instance] _root_.Algebra.TensorProduct.rightAlgebra

/-- Quotienting a pushout by the extension of an ideal gives the corresponding pushout.
The supplied algebra structure on the quotient is retained. -/
theorem isPushout_quotient_of_compatible_map
    {A : Type u} {B : Type v} {Q : Type w} {Q' : Type x}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing Q']
    [Algebra A B] [Algebra A Q] [Algebra A Q'] [Algebra B Q'] [Algebra Q Q']
    [IsScalarTower A B Q'] [IsScalarTower A Q Q']
    [_root_.Algebra.IsPushout A B Q Q']
    (I : Ideal Q)
    [Algebra (Q ⧸ I) (Q' ⧸ I.map (algebraMap Q Q'))]
    [IsScalarTower A (Q ⧸ I) (Q' ⧸ I.map (algebraMap Q Q'))]
    (hmap : (algebraMap (Q ⧸ I) (Q' ⧸ I.map (algebraMap Q Q'))).comp
        (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap Q Q'))).comp (algebraMap Q Q')) :
    _root_.Algebra.IsPushout A B (Q ⧸ I) (Q' ⧸ I.map (algebraMap Q Q')) := by
  let e₀ := _root_.Algebra.IsPushout.equiv A B Q Q'
  have he : I.map (algebraMap Q Q') =
      (I.map (_root_.Algebra.TensorProduct.includeRight (R := A) (A := B))).map
        (e₀ : B ⊗[A] Q →+* Q') := by
    change I.map (algebraMap Q Q') =
      (I.map (_root_.Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom).map
        (e₀ : B ⊗[A] Q →+* Q')
    rw [Ideal.map_map]
    congr 1
    ext q
    simp [e₀, _root_.Algebra.IsPushout.equiv_tmul]
  let e : B ⊗[A] (Q ⧸ I) ≃ₐ[B] Q' ⧸ I.map (algebraMap Q Q') :=
    (_root_.Algebra.TensorProduct.tensorQuotientEquiv B Q B I).trans
      (Ideal.quotientEquivAlg _ _ e₀ he)
  refine ⟨IsBaseChange.of_equiv e.toLinearEquiv ?_⟩
  intro q
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
  change e (1 ⊗ₜ[A] Ideal.Quotient.mk I q) = _
  simp only [e, AlgEquiv.trans_apply,
    _root_.Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk]
  rw [_root_.Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  exact (DFunLike.congr_fun hmap q).symm

end Langlands.Algebra
