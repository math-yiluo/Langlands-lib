import Langlands.Global.Arithmetic.FiniteArtinUnramifiedCriterion
import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtin
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinNormalization
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinUnramified

/-!
# Proof of the unit criterion for normalized Artin maps

This file proves `Langlands.Global.FiniteArtinUnramifiedCriterionStatement`: if a continuous
surjective homomorphism from the idèle classes of a number field `K` to the Galois group of a
finite abelian extension `E / K`, with the discrete topology and the Library's arithmetic
normalization, kills the local units at a finite place `v`, then every prime of `E` above `v` is
unramified over `K`.

By the uniqueness of a normalized map (`eq_of_hasArithmeticArtinNormalization`) the map is the
arithmetic Artin map `arithmeticFiniteArtinBot K E`; the unit criterion for that map is
`isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one`
(`Langlands/ClassFieldTheory/Global/Artin/FiniteArtinUnramified.lean`). Surjectivity is not used.
-/

noncomputable section

universe uK uE

namespace Langlands.Global

open Langlands.ClassFieldTheory.Global.Artin

/-- A normalized map that kills the local units at `v` belongs to an extension unramified above
`v`. -/
theorem finiteArtinUnramifiedCriterion : FiniteArtinUnramifiedCriterionStatement.{uK, uE} := by
  intro K _ _ E _ _ _ _ hcomm ρ _ hnorm v hunits w hw
  have : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  have : IsAbelianGalois K E := { toIsMulCommutative := IsMulCommutative.of_comm hcomm }
  let : TopologicalSpace (E ≃ₐ[K] E) := ⊥
  have hρ : ρ = arithmeticFiniteArtinBot K E :=
    eq_of_hasArithmeticArtinNormalization ρ _ hnorm
      arithmeticFiniteArtin_hasArithmeticArtinNormalization
  refine isUnramifiedAt_of_arithmeticFiniteArtin_finiteClassInclusion_eq_one v
    (fun a ha => ?_) w hw
  have h := hunits a ha
  rw [hρ] at h
  exact h

end Langlands.Global
