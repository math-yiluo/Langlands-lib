import Langlands.Weil.Representation.InductionFinitenessStatements
import Langlands.Weil.Representation.Induction

/-!
# Dimension and rank of finite-index Weil induction

Mathlib's finite-index comparison transports the coset-coordinate dimension count
from equivariant functions to the actual tensor/coinvariant carrier `IndV`.
-/

noncomputable section

namespace Langlands.Weil

universe uG uV

/-- The actual induced carrier is finite-dimensional, of rank index times rank. -/
theorem representationInductionDimension :
    RepresentationInductionDimension.{uG, uV} := by
  intro G _ H _ V _ _ _ ρ
  classical
  let A : FiniteRepresentation.{0, uG, uV} ℂ H := FiniteRepresentation.of ρ
  let e : Representation.IndV H.subtype ρ ≃ₗ[ℂ] Representation.coindV H.subtype ρ :=
    (Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))).toLinearEquiv
  have : FiniteDimensional ℂ (Representation.coindV H.subtype ρ) :=
    FiniteRepresentation.finite_coindV H A
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq]
  exact FiniteRepresentation.rank_induce H A

-- Check the complete unapplied constant, preserving both universe parameters.
example : RepresentationInductionDimension.{uG, uV} :=
  @representationInductionDimension.{uG, uV}

-- The same constant against the unfolded statement, with independent universes.
example :
    ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
      (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ H V),
      FiniteDimensional ℂ (Representation.IndV H.subtype ρ) ∧
      Module.finrank ℂ (Representation.IndV H.subtype ρ) =
        H.index * Module.finrank ℂ V :=
  @representationInductionDimension.{uG, uV}

end Langlands.Weil
