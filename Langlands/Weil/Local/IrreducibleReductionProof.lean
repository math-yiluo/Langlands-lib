import Langlands.Weil.Local.GaloisCorrectionProof
import Langlands.Weil.Local.CharacterNormProof

/-! # Irreducible scalar reduction on the actual local Weil group -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

/-- The existing irreducible unramified-twist and determinant-order statement. -/
theorem localWeilIrreducibleReductionFor {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) : LocalWeilIrreducibleReductionFor.{u, v} F := by
  let : CompactSpace (localDegree F).toMonoidHom.ker := isCompact_iff_compactSpace.mp
    (localInertia_isCompact F)
  let := localWeilGroup_nonarchimedean F
  intro A hc hirr
  let := A.carrierNormedAddCommGroup
  let := A.carrierNormedSpace
  obtain ⟨⟨χ, σ, _, hχi, hσc, hσf, hσirr, heq⟩, hdet⟩ :=
    (unramifiedReduction (localWeilGroup F) (localDegree F).toMonoidHom
      (localDegree_surjective F) (localInertia_isOpen F) A A.representation
      ((FiniteRepresentation.isContinuous_of_iff _).mp hc)).2 hirr
  obtain ⟨_, z, ⟨hz, _⟩, _⟩ := (localUnramifiedCharacterClassificationFor F χ).mp hχi
  let B : LocalWeilRepresentation.{u, v} F := FiniteRepresentation.of σ
  have hBc : B.IsContinuous := (FiniteRepresentation.isContinuous_of_iff σ).mpr hσc
  refine ⟨⟨z, B, hBc, hσirr, hσf, ((localWeilGaloisTypeFor F B).1).mpr ⟨hBc, hσf⟩,
    ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun g => ?_⟩⟩, hdet⟩
  change A.representation g = Langlands.twist (localUnramifiedCharacter F z).toMonoidHom σ g
  rw [hz, ← heq]

end Langlands.Weil.Local
