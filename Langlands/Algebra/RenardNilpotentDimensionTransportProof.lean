import Langlands.Algebra.RenardNilpotentDimensionTransportStatement
import Langlands.Algebra.CommutingDimensionRecurrence

/-! Carrier invariance of Renard's actual nilpotent-generated dimension maximum. -/

noncomputable section

universe u v

namespace Langlands.Renard

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

private theorem nilpotentGeneratedDimensions_subset_of_linearEquiv
    (l : ℕ) (e : V ≃ₗ[ℂ] W) :
    nilpotentGeneratedDimensions l V ⊆ nilpotentGeneratedDimensions l W := by
  intro d hd
  obtain ⟨a, hcomm, hnil, ha⟩ := hd
  refine ⟨fun i => e.conjAlgEquiv ℂ (a i), ?_, ?_, ?_⟩
  · intro i j
    exact (hcomm i j).map (e.conjAlgEquiv ℂ).toAlgHom
  · intro i
    exact (hnil i).map (e.conjAlgEquiv ℂ).toAlgHom
  · exact (Langlands.CommutingDimension.finrank_adjoin_map
      ℂ a (e.conjAlgEquiv ℂ).toAlgHom (e.conjAlgEquiv ℂ).injective).symm.trans ha

/-- Conjugation preserves the exact set of attainable generated-algebra dimensions. -/
theorem nilpotentGeneratedDimensions_eq_of_linearEquiv
    (l : ℕ) (e : V ≃ₗ[ℂ] W) :
    nilpotentGeneratedDimensions l V = nilpotentGeneratedDimensions l W :=
  Set.Subset.antisymm
    (nilpotentGeneratedDimensions_subset_of_linearEquiv l e)
    (nilpotentGeneratedDimensions_subset_of_linearEquiv l e.symm)

/-- Equal dimension sets give equal actual natural-supremum maxima. -/
theorem nilpotentGeneratedMaxDimension_eq_of_linearEquiv
    (l : ℕ) (e : V ≃ₗ[ℂ] W) :
    nilpotentGeneratedMaxDimension l V = nilpotentGeneratedMaxDimension l W := by
  unfold nilpotentGeneratedMaxDimension
  rw [nilpotentGeneratedDimensions_eq_of_linearEquiv l e]

/-- The exact transport proposition, including its canonical-carrier identification. -/
theorem nilpotentDimensionTransport : NilpotentDimensionTransportStatement.{u, v} := by
  constructor
  · intro l V _ _ _ W _ _ _ e
    exact ⟨nilpotentGeneratedDimensions_eq_of_linearEquiv l e,
      nilpotentGeneratedMaxDimension_eq_of_linearEquiv l e⟩
  · intro l V _ _ _
    exact nilpotentGeneratedMaxDimension_eq_of_linearEquiv l
      (Module.finBasis ℂ V).equivFun

end Langlands.Renard
