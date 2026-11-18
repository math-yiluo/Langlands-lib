import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Lifting standard étale algebras across quotient maps -/

noncomputable section

universe u v

open Polynomial
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.StandardEtaleLift

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Invert the derivative as well as the chosen localization polynomial. -/
def derivativePair (f : R[X]) (hf : f.Monic) (g : R[X]) : StandardEtalePair R where
  f := f
  monic_f := hf
  g := f.derivative * g
  cond := ⟨g, 0, 1, by simp⟩

/-- Adding the already invertible derivative to the localization does not change
the algebra of a standard étale presentation. -/
def derivativePairEquiv (P : StandardEtalePresentation R S) :
    (derivativePair P.f P.monic_f P.g).Ring ≃ₐ[R] S := by
  let Q := derivativePair P.f P.monic_f P.g
  have hQ : Q.HasMap P.x :=
    ⟨P.hasMap.1, by
      change IsUnit (aeval P.x (P.f.derivative * P.g))
      rw [map_mul]
      exact P.hasMap.isUnit_derivative_f.mul P.hasMap.2⟩
  have hP : P.P.HasMap Q.X :=
    ⟨Q.hasMap_X.1, by
      have h := Q.hasMap_X.2
      change IsUnit (aeval Q.X (P.f.derivative * P.g)) at h
      rw [map_mul] at h
      exact isUnit_of_mul_isUnit_right h⟩
  let f : Q.Ring →ₐ[R] S := Q.lift P.x hQ
  let g : S →ₐ[R] Q.Ring := (P.P.lift Q.X hP).comp P.equivRing.toAlgHom
  have hf : f Q.X = P.x := Q.lift_X _ _
  have hg : g P.x = Q.X := by
    change P.P.lift Q.X hP (P.equivRing P.x) = Q.X
    rw [P.equivRing_x, P.P.lift_X]
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply P.hom_ext
    change f (g P.x) = P.x
    rw [hg, hf]
  · apply Q.hom_ext
    change g (f Q.X) = Q.X
    rw [hf, hg]

private theorem pair_ext {P Q : StandardEtalePair R}
    (hf : P.f = Q.f) (hg : P.g = Q.g) : P = Q := by
  cases P
  cases Q
  cases hf
  cases hg
  rfl

/-- A standard étale presentation over a quotient of the coefficient ring has
a standard étale lift, up to coefficient-base-change isomorphism. -/
theorem exists_pair_map_equiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra B C] (r : A →+* B) (hr : Function.Surjective r)
    (P : StandardEtalePresentation B C) :
    ∃ Q : StandardEtalePair A, Nonempty ((Q.map r).Ring ≃ₐ[B] C) := by
  obtain ⟨f, hf, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hr P.f) P.monic_f
  obtain ⟨g, hg⟩ := (Polynomial.mem_lifts (f := r) P.g).mp
    (Polynomial.mem_lifts_of_surjective hr P.g)
  let Q := derivativePair f hmonic g
  have hQ : Q.map r = derivativePair P.f P.monic_f P.g := by
    apply pair_ext
    · exact hf
    · change (f.derivative * g).map r = P.f.derivative * P.g
      rw [Polynomial.map_mul, ← Polynomial.derivative_map, hf, hg]
  refine ⟨Q, ?_⟩
  rw [hQ]
  exact ⟨derivativePairEquiv P⟩

/-- Every standard étale algebra over a quotient has a lift with the correct
tensor-product reduction. No nilpotence assumption is needed for this local construction. -/
theorem exists_pair_tensor_equiv (A : Type u) [CommRing A] (J : Ideal A)
    (S : Type v) [CommRing S] [Algebra (A ⧸ J) S] [Algebra.IsStandardEtale (A ⧸ J) S] :
    ∃ Q : StandardEtalePair A, Nonempty ((A ⧸ J) ⊗[A] Q.Ring ≃ₐ[A ⧸ J] S) := by
  let P : StandardEtalePresentation (A ⧸ J) S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨Q, ⟨e⟩⟩ := exists_pair_map_equiv (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective P
  let QP : StandardEtalePresentation A Q.Ring :=
    ⟨Q, Q.X, Q.hasMap_X, by
      rw [StandardEtalePair.lift_X_left]
      exact Function.bijective_id⟩
  exact ⟨Q, ⟨QP.baseChange.equivRing.trans e⟩⟩

/-- A standard étale algebra over `A ⧸ J` is the quotient of an étale
`A`-algebra by the ideal extended from `J`. -/
theorem exists_etale_quotient_lift (A : Type u) [CommRing A] (J : Ideal A)
    (S : Type u) [CommRing S] [Algebra (A ⧸ J) S] [Algebra.IsStandardEtale (A ⧸ J) S] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      ∃ q : B →+* S, q.comp (algebraMap A B) =
        (algebraMap (A ⧸ J) S).comp (Ideal.Quotient.mk J) ∧
        Function.Surjective q ∧ RingHom.ker q = J.map (algebraMap A B) := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_pair_tensor_equiv A J S
  let I := J.map (algebraMap A Q.Ring)
  let d : (Q.Ring ⧸ I) ≃ₐ[A ⧸ J] S :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Q.Ring J).trans e
  let q := d.toRingHom.comp (Ideal.Quotient.mk I)
  refine ⟨Q.Ring, inferInstance, inferInstance, inferInstance, q, ?_,
    d.surjective.comp Ideal.Quotient.mk_surjective, ?_⟩
  · ext x
    change d (algebraMap A (Q.Ring ⧸ I) x) = algebraMap (A ⧸ J) S (Ideal.Quotient.mk J x)
    rw [IsScalarTower.algebraMap_apply A (A ⧸ J) (Q.Ring ⧸ I), d.commutes]
    rfl
  · rw [RingHom.ker_comp_of_injective _ d.injective, Ideal.mk_ker]

/-- For a nilpotent `J`, the quotient map of the chart lift has nilpotent kernel. -/
theorem exists_etale_nilpotent_lift (A : Type u) [CommRing A] (J : Ideal A)
    (hJ : IsNilpotent J) (S : Type u) [CommRing S] [Algebra (A ⧸ J) S]
    [Algebra.IsStandardEtale (A ⧸ J) S] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      ∃ q : B →+* S, q.comp (algebraMap A B) =
        (algebraMap (A ⧸ J) S).comp (Ideal.Quotient.mk J) ∧
        Function.Surjective q ∧ IsNilpotent (RingHom.ker q) := by
  obtain ⟨B, hB, hA, he, q, hq, hs, hk⟩ := exists_etale_quotient_lift A J S
  refine ⟨B, hB, hA, he, q, hq, hs, ?_⟩
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [hk, ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩

end Langlands.AlgebraicGeometry.StandardEtaleLift
