import Langlands.GroupScheme.Reductive.SteinbergCovariantExhaustionStatement
import Langlands.GroupScheme.Reductive.SteinbergTensorEmbeddingStatement
import Langlands.GroupScheme.Reductive.CovariantTensorEmbedding

/-! # Steinberg tensor embeddings from covariant exhaustion -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Covariant exhaustion by Steinberg-type products implies the Steinberg
tensor-embedding input. -/
def SteinbergTensorEmbeddingFromCovariantStatement : Prop :=
  SteinbergCovariantExhaustionStatement.{u} → SteinbergTensorEmbeddingStatement.{u}

/-- Proof of the reduction: injectivity of the difference comorphism makes multiplication
injective on products of covariant spaces, and exhaustion with cofinal irreducibility
places each finite invariant subspace in one such product. -/
theorem steinbergTensorEmbedding_of_covariantExhaustion :
    SteinbergTensorEmbeddingFromCovariantStatement.{u} := by
  intro hS k _ _ p _ _ G _ hG
  have : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  obtain ⟨Λ, _, j, H, H', _, _, i, i', χ, ψ, hdense, hone, hexh, hst⟩ := hS k p G hG
  exact ⟨Λ, inferInstance, j, fun V d b hV hinv =>
    Chevalley.exists_tensor_embedding_of_covariant_exhaustion G j i i' χ ψ hdense hone hexh
      hst V b hV hinv⟩

end Langlands.GroupScheme
