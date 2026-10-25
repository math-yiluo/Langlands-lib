import Langlands.ClassField.Global.CyclicUnitHerbrandQuotientStatement
import Langlands.ClassField.Global.FullLogLatticeSequence
import Langlands.Cohomology.HerbrandLattice
import Langlands.Cohomology.HerbrandPermutation

/-! # The cyclic Herbrand quotient of ordinary units -/

noncomputable section

universe u v

namespace Langlands.ClassField.Global

open NumberField CategoryTheory Langlands.Cohomology.Herbrand

/-- The actual ordinary units satisfy the cyclic Herbrand formula, including torsion. -/
theorem cyclicUnitHerbrandQuotient : CyclicUnitHerbrandQuotient.{u,v} := by
  intro F _ _ E _ _ _ _ _
  have hN : HasHerbrandQuotient (infinitePlaceLatticeRepresentation F E)
      (archimedeanHerbrandFactor F E) :=
    hasHerbrandQuotient_ofMulAction (G := E ≃ₐ[F] E) (X := InfinitePlace E)
  have hM : HasHerbrandQuotient (augmentedFullLogUnitLatticeRepresentation F E)
      (archimedeanHerbrandFactor F E) := by
    apply (hasHerbrandQuotient_iff_of_isZLattice
      (fun g : E ≃ₐ[F] E => (fullLogPermutation F E g).toLinearMap)
      (infinitePlaceCoordinateLattice E) (augmentedFullLogUnitLattice E)
      (infinitePlaceLatticeRealization F E).toAddEquiv
      (AddEquiv.refl (augmentedFullLogUnitLattice E))
      (fun g x => ?_) (fun _ _ => rfl)).mp hN
    exact congrArg (fun x : infinitePlaceCoordinateLattice E =>
      (x : InfinitePlace E → ℝ)) (infinitePlaceLatticeRealization_equivariant F E g x)
  have hZ : HasHerbrandQuotient (fullLogLatticeSequence F E).X₃
      (Module.finrank F E) := by
    have h := hasHerbrandQuotient_trivialIntegers (G := E ≃ₐ[F] E)
    rwa [IsGalois.card_aut_eq_finrank F E] at h
  have hM0 := HasHerbrandQuotient.of_shortExact_left
    (fullLogLatticeSequence_shortExact F E) hM hZ
  have hU0 : HasHerbrandQuotient (unitsModuloTorsionRepresentation F E)
      ((archimedeanHerbrandFactor F E : ℚ) / Module.finrank F E) :=
    HasHerbrandQuotient.of_linearEquiv
      (fullLogEmbeddingCohomologyIso F E 1).symm.toLinearEquiv
      (fullLogEmbeddingCohomologyIso F E 2).symm.toLinearEquiv hM0
  have : Finite (unitTorsionRepresentation F E) := unitTorsionRepresentation_finite F E
  have hT := hasHerbrandQuotient_of_finite (unitTorsionRepresentation F E)
  have hU : HasHerbrandQuotient (ringIntegerUnitsRepresentation F E)
      ((archimedeanHerbrandFactor F E : ℚ) / Module.finrank F E) := by
    simpa only [unitTorsionSequence, one_mul] using HasHerbrandQuotient.of_shortExact
      (unitTorsionSequence_shortExact F E) hT hU0
  refine ⟨hU.1, hU.2.1, ?_⟩
  have hn : (Module.finrank F E : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := E)).ne'
  have h : (Module.finrank F E : ℚ) *
      Nat.card (groupCohomology (ringIntegerUnitsRepresentation F E) 2) =
        archimedeanHerbrandFactor F E *
          Nat.card (groupCohomology (ringIntegerUnitsRepresentation F E) 1) := by
    rw [hU.2.2]
    field_simp
  exact_mod_cast h

end Langlands.ClassField.Global
