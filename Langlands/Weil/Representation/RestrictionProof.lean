import Langlands.Weil.Representation.RestrictionInduction

/-!
# Generic restriction laws for complex Weil representations

All ten clauses use precomposition of the original Mathlib action. The inertia
clauses use the map from the supplied source inertia into the target inertia.
-/

noncomputable section

namespace Langlands.Weil

universe uG uH uV uU

/-- Restriction preserves the predicates and operations in the exact generic target. -/
theorem representationRestriction : RepresentationRestriction.{uG, uH, uV, uU} := by
  intro G _ _ H _ _ φ I J hφ hJI V _ _ _ U _ _ _ ρ σ
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  let f : J → I := fun j => ⟨φ (j : H), hJI j.property⟩
  have hf : Continuous f := (hφ.comp continuous_subtype_val).subtype_mk _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hρ
    exact hρ.comp hφ
  · intro hρ
    exact hρ.preimage hf
  · intro hρ
    exact hρ.subset (Set.range_comp_subset_range f (ρ.comp I.subtype))
  · intro hρ
    exact hρ.subset (Set.range_comp_subset_range φ ρ)
  · intro hρ j
    exact hρ (f j)
  · rfl
  · rfl
  · apply MonoidHom.ext
    intro h
    simp only [MonoidHom.comp_apply, Representation.dual_apply, map_inv]
  · intro h
    rfl
  · rintro ⟨e⟩
    exact ⟨Representation.Equiv.mk e.toLinearEquiv
      (fun h => e.isIntertwining' (φ h))⟩

-- Check the entire unapplied closing constant, with all universes independent.
example : RepresentationRestriction.{uG, uH, uV, uU} :=
  @representationRestriction.{uG, uH, uV, uU}

end Langlands.Weil
