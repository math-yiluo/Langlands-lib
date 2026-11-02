import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineMapStatements

/-!
# Quotient and coefficient-map proofs for affine point topologies
-/

noncomputable section

universe u v w x y

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

variable {R : Type u} {A : Type v} {B : Type w} {S : Type x} {T : Type y}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing S] [CommRing T]
variable [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]
variable [TopologicalSpace S] [TopologicalSpace T]

theorem quotientPointEmbeddingProperties_proof :
    QuotientPointEmbeddingProperties R A B S := by
  intro f hf
  refine ⟨AlgPoint.isEmbedding_precomp_of_surjective f hf, ?_⟩
  intro hT2
  exact AlgPoint.isClosedEmbedding_precomp_of_surjective f hf

namespace AlgPoint

theorem isEmbedding_mapCoefficients (f : S →ₐ[R] T) (hf : IsEmbedding f) :
    IsEmbedding (mapCoefficients (A := A) f) := by
  have h : IsEmbedding (fun z : A → S => fun a : A => f (z a)) :=
    IsEmbedding.piMap (fun _ => hf)
  exact IsEmbedding.of_comp (continuous_mapCoefficients f hf.continuous)
    continuous_evaluation (h.comp isEmbedding_evaluation)

omit [TopologicalSpace S] [TopologicalSpace T] in
theorem range_mapCoefficients (f : S →ₐ[R] T) (hf : Function.Injective f) :
    Set.range (mapCoefficients (A := A) f) =
      ⋂ a : A, {p : AlgPoint R A T | p a ∈ Set.range f} := by
  ext p
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, rfl⟩ a
    exact ⟨q a, rfl⟩
  · intro hp
    have hm : ∀ a, p a ∈ f.range := hp
    let e := AlgEquiv.ofInjective f hf
    let q : A →ₐ[R] S := e.symm.toAlgHom.comp (p.toAlgHom.codRestrict f.range hm)
    refine ⟨ofAlgHom q, ?_⟩
    ext a
    exact congrArg (fun z : f.range => (z : T)) (e.apply_symm_apply ⟨p a, hm a⟩)

theorem isClosedEmbedding_mapCoefficients (f : S →ₐ[R] T)
    (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (mapCoefficients (A := A) f) := by
  refine ⟨isEmbedding_mapCoefficients f hf.isEmbedding, ?_⟩
  rw [range_mapCoefficients f hf.injective]
  exact isClosed_iInter (fun a => hf.isClosed_range.preimage (continuous_eval a))

theorem isOpenEmbedding_mapCoefficients (hA : Algebra.FiniteType R A)
    (f : S →ₐ[R] T) (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (mapCoefficients (A := A) f) := by
  obtain ⟨s, hs⟩ := hA.out
  refine ⟨isEmbedding_mapCoefficients f hf.isEmbedding, ?_⟩
  have hr : Set.range (mapCoefficients (A := A) f) =
      ⋂ a ∈ s, {p : AlgPoint R A T | p a ∈ Set.range f} := by
    rw [range_mapCoefficients f hf.injective]
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · exact fun hp a _ => hp a
    · intro hp a
      have hsub : Algebra.adjoin R (↑s : Set A) ≤ f.range.comap p.toAlgHom :=
        Algebra.adjoin_le (fun a ha => hp a ha)
      rw [hs] at hsub
      exact hsub (Algebra.mem_top : a ∈ (⊤ : Subalgebra R A))
  rw [hr]
  exact isOpen_biInter_finset (fun a _ =>
    hf.isOpen_range.preimage (continuous_eval a))

end AlgPoint

theorem coefficientEmbeddingProperties_proof :
    CoefficientEmbeddingProperties R A S T := by
  intro f
  exact ⟨AlgPoint.isEmbedding_mapCoefficients f, AlgPoint.isClosedEmbedding_mapCoefficients f⟩

theorem coefficientOpenEmbeddingProperty_proof
    [IsTopologicalRing S] [IsTopologicalRing T] :
    CoefficientOpenEmbeddingProperty R A S T := by
  intro hA f hf
  exact AlgPoint.isOpenEmbedding_mapCoefficients hA f hf

theorem affineDiscreteProperty_proof [IsTopologicalRing S] [DiscreteTopology S] :
    AffineDiscreteProperty R A S := by
  intro hA
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  exact ((AlgPoint.polynomialPointHomeomorph (R := R) (S := S) (Fin n)).isEmbedding.comp
    (AlgPoint.isEmbedding_precomp_of_surjective f hf)).discreteTopology

theorem affineMapProperties_proof : AffineMapProperties R A B S T := by
  refine ⟨quotientPointEmbeddingProperties_proof, coefficientEmbeddingProperties_proof, ?_, ?_⟩
  · intro hS hT
    exact coefficientOpenEmbeddingProperty_proof
  · intro hS hD
    exact affineDiscreteProperty_proof

end Langlands.AlgebraicGeometry.PointTopology
