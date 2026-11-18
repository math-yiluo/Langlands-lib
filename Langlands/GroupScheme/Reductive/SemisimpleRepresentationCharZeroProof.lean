import Langlands.GroupScheme.Reductive.SemisimpleRepresentationCharZeroStatement
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationUnipotentProof
import Langlands.GroupScheme.MatrixRepresentation.InvariantIntegralSemisimple
import Langlands.GroupScheme.Reductive.CharacteristicZeroInvariantIntegralProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Characteristic-zero reductivity and semisimple representations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A connected affine algebraic group in characteristic zero is reductive
exactly when all its finite representations are semisimple, or equivalently
when it has a faithful semisimple finite representation. -/
theorem charZeroReductiveSemisimpleRepresentation :
    CharZeroReductiveSemisimpleRepresentationStatement.{u} := by
  intro k _ _ G _ _ hconnected
  change (IsConnectedReductive G ↔
      ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), ρ.IsSemisimple) ∧
    (IsConnectedReductive G ↔
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        IsClosedSubgroup ρ ∧ ρ.IsSemisimple)
  have hforward (hG : IsConnectedReductive G)
      (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) : ρ.IsSemisimple := by
    obtain ⟨I⟩ := characteristicZeroReductiveInvariantIntegral k G hG
    exact ρ.isSemisimple_of_invariantIntegral I
  obtain ⟨N, σ, hσ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have hreverse
      (h : ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        IsClosedSubgroup ρ ∧ ρ.IsSemisimple) : IsConnectedReductive G := by
    obtain ⟨n, ρ, hρ, hsemi⟩ := h
    have hsmooth : Smooth G.X.hom :=
      affineCartierSmooth k G inferInstance inferInstance
    have hrad : HasTrivialUnipotentRadical G :=
      (semisimpleRepresentationUnipotent k G).2 hsmooth hconnected n ρ hρ hsemi
    exact (perfectFieldPseudoReductive k G).mp
      ⟨hsmooth, inferInstance, hconnected, hrad⟩
  exact ⟨⟨hforward, fun h => hreverse ⟨N, σ, hσ, h N σ⟩⟩,
    ⟨fun hG => ⟨N, σ, hσ, hforward hG N σ⟩, hreverse⟩⟩

end Langlands.GroupScheme
