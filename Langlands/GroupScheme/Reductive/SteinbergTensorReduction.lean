import Langlands.GroupScheme.Reductive.SteinbergTensorEmbeddingStatement
import Langlands.GroupScheme.Reductive.NondegenerateTensorConjugation
import Langlands.GroupScheme.Reductive.PositiveCharConjugationMapStatement

/-! # The positive-characteristic conjugation map from Steinberg tensor embeddings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineLinearEmbedding MatrixRepresentation

/-- The coordinate algebra of an affine group scheme over a field is nontrivial:
its counit is an algebra map to the field. -/
theorem AffineCoordinates.nontrivial_algebra {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left] :
    Nontrivial (AffineCoordinates.algebra G) := by
  letI := bialgebra (AffineCoordinates.corepresentation G)
  exact (Bialgebra.counitAlgHom k (AffineCoordinates.algebra G)).toRingHom.domain_nontrivial

/-- The Steinberg tensor-embedding input implies the simply connected
positive-characteristic conjugation-map input to Haboush's theorem. -/
def SimplyConnectedPositiveCharConjugationMapFromSteinbergStatement : Prop :=
  SteinbergTensorEmbeddingStatement.{u} →
    SimplyConnectedPositiveCharConjugationMapStatement.{u}

/-- Proof of the reduction: the Reynolds-normalized regular target of a fixed vector
embeds into a tensor product with irreducible first factor, and the nondegenerate
tensor adapter turns the resulting nonzero fixed tensor into a conjugation map with
the identity matrix as value. -/
theorem simplyConnectedPositiveCharConjugationMap_of_steinberg :
    SimplyConnectedPositiveCharConjugationMapFromSteinbergStatement.{u} := by
  intro hS k _ _ p _ _ G hG n _ _ ρ v hv0 hv
  haveI : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨Λ, _, j, hj⟩ := hS k p G hG
  obtain ⟨V, d, b, hV, C, hC, -, hinv, h1⟩ :=
    Chevalley.exists_affine_finite_diagonalizable_regular_map_to_one j ρ v hv0 hv
  obtain ⟨m, σ, π, E, hσ, hE, hinj⟩ := hj V d b hV hinv
  have hCv : C *ᵥ v ≠ 0 := by
    intro h0
    haveI := AffineCoordinates.nontrivial_algebra G
    apply (zero_ne_one : (0 : AffineCoordinates.algebra G) ≠ 1)
    rw [← h1, h0]
    simp
  have hEC : (E * C) *ᵥ v ≠ 0 := by
    rw [← Matrix.mulVec_mulVec]
    intro h0
    apply hCv
    apply hinj
    change E *ᵥ (C *ᵥ v) = E *ᵥ 0
    rw [h0, Matrix.mulVec_zero]
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd (funext fun x => x.1.elim0) hEC
    · exact h
  obtain ⟨φ, hφ⟩ :=
    ConjugationLinearMap.exists_eval_eq_one_of_tensor hσ (hC.comp hE) v hv hEC
  exact ⟨m, hm, σ, φ, 1, one_ne_zero, by rw [hφ, one_smul]⟩

end Langlands.GroupScheme
