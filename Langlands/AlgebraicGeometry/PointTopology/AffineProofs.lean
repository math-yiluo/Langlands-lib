import Langlands.AlgebraicGeometry.PointTopology.AffineStatements
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Finite-coordinate affine topology proofs

Proofs of the finite-coordinate part of Conrad, Proposition 2.1.
-/

noncomputable section

universe u v w z

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
variable [TopologicalSpace S]

namespace AlgPoint

theorem isEmbedding_precomp_of_surjective {B : Type z} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    IsEmbedding (precomp (S := S) f) := by
  let l : B → A := Function.surjInv hf
  have hl : ∀ b, f (l b) = b := Function.rightInverse_surjInv hf
  have hc : Continuous (fun z : A → S => fun b : B => z (l b)) :=
    continuous_pi (fun b => continuous_apply (l b))
  have he : IsEmbedding (fun p : AlgPoint R B S => fun a : A => p (f a)) := by
    apply IsEmbedding.of_comp (continuous_pi (fun a => continuous_eval (f a))) hc
    convert (isEmbedding_evaluation (R := R) (A := B) (S := S)) using 1
    funext p b
    exact congrArg p (hl b)
  exact IsEmbedding.of_comp (continuous_precomp f) continuous_evaluation he

theorem isClosedEmbedding_precomp_of_surjective [T2Space S]
    {B : Type z} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    IsClosedEmbedding (precomp (S := S) f) := by
  refine ⟨isEmbedding_precomp_of_surjective f hf, ?_⟩
  have hr : Set.range (precomp (S := S) f) =
      ⋂ a : RingHom.ker f.toRingHom, {p : AlgPoint R A S | p a = 0} := by
    ext p
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, rfl⟩ a
      change q (f a) = 0
      rw [show f a = 0 from a.property]
      exact map_zero q.toAlgHom
    · intro hp
      have hk : RingHom.ker f.toRingHom ≤ RingHom.ker p.toAlgHom.toRingHom := by
        intro a ha
        exact hp ⟨a, ha⟩
      refine ⟨ofAlgHom (f.liftOfSurjective hf p.toAlgHom hk), ?_⟩
      ext a
      exact AlgHom.liftOfSurjective_apply f hf p.toAlgHom hk a
  rw [hr]
  exact isClosed_iInter (fun a => isClosed_eq (continuous_eval (a : A)) continuous_const)

variable [IsTopologicalRing S]

/-- Polynomial points are their generator values, with the actual product topology. -/
def polynomialPointHomeomorph (ι : Type z) :
    AlgPoint R (MvPolynomial ι R) S ≃ₜ (ι → S) where
  toFun p i := p (MvPolynomial.X i)
  invFun x := ofAlgHom (MvPolynomial.aeval x)
  left_inv p := by
    apply algHomEquiv.injective
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ _
  right_inv x := by
    funext i
    exact MvPolynomial.aeval_X x i
  continuous_toFun := continuous_pi (fun i => continuous_eval _)
  continuous_invFun := by
    apply (continuous_iff _).mpr
    intro P
    change Continuous (fun x : ι → S => MvPolynomial.aeval x P)
    induction P using MvPolynomial.induction_on with
    | C r =>
        simpa only [MvPolynomial.aeval_C] using
          (continuous_const : Continuous (fun _ : ι → S => algebraMap R S r))
    | add p q hp hq =>
        simpa only [map_add] using hp.fun_add hq
    | mul_X p i hp =>
        simpa only [map_mul, MvPolynomial.aeval_X] using
          hp.fun_mul (continuous_apply i)

end AlgPoint

variable (R A S)
variable [IsTopologicalRing S]

theorem finiteCoordinateEmbedding_proof : FiniteCoordinateEmbedding R A S := by
  intro n a ha
  have hf : Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A) :=
    (AlgHom.range_eq_top _).mp ((MvPolynomial.aeval_range a).trans ha)
  have h := (AlgPoint.polynomialPointHomeomorph (R := R) (S := S) (Fin n)).isEmbedding.comp
    (AlgPoint.isEmbedding_precomp_of_surjective _ hf)
  change IsEmbedding (fun (p : AlgPoint R A S) (i : Fin n) =>
    p (MvPolynomial.aeval a (MvPolynomial.X i))) at h
  simpa only [MvPolynomial.aeval_X] using h

theorem finiteCoordinateClosedEmbedding_proof [T2Space S] :
    FiniteCoordinateClosedEmbedding R A S := by
  intro n a ha
  have hf : Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A) :=
    (AlgHom.range_eq_top _).mp ((MvPolynomial.aeval_range a).trans ha)
  have h := (AlgPoint.polynomialPointHomeomorph (R := R) (S := S) (Fin n)).isClosedEmbedding.comp
    (AlgPoint.isClosedEmbedding_precomp_of_surjective _ hf)
  change IsClosedEmbedding (fun (p : AlgPoint R A S) (i : Fin n) =>
    p (MvPolynomial.aeval a (MvPolynomial.X i))) at h
  simpa only [MvPolynomial.aeval_X] using h

theorem affineLocalCompactness_proof [T2Space S] [LocallyCompactSpace S] :
    AffineLocalCompactness R A S := by
  intro hA
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  exact ((AlgPoint.polynomialPointHomeomorph (R := R) (S := S) (Fin n)).isClosedEmbedding.comp
    (AlgPoint.isClosedEmbedding_precomp_of_surjective f hf)).locallyCompactSpace

theorem affineCoordinateProperties_proof : AffineCoordinateProperties R A S := by
  refine ⟨finiteCoordinateEmbedding_proof R A S, ?_, ?_⟩
  · intro hT2
    exact finiteCoordinateClosedEmbedding_proof R A S
  · intro hT2 hLC
    exact affineLocalCompactness_proof R A S

end Langlands.AlgebraicGeometry.PointTopology
