import Langlands.LocalFactor.Ramification.Herbrand.LocalSubextensionStatement

/-!
# Herbrand's finite subgroup formula in either characteristic

For a tower `K → E → M` inside one realization `T` of `M/K₀`, restriction of
scalars from `E` to `K` does not change the action of an automorphism on the
integer ring `T.Integers`, so it preserves every integer lower group. The upper
group of `M/K` at `u` is the lower group at `ψ_{M/K}(u)`, and the upper group of
`M/E` at `φ_{M/E}(t)` is the lower group at `t`; taking `t = ψ_{M/K}(u)` gives the
formula.
-/

namespace Langlands.Ramification.Local

universe u₀ uK uE uM

section Lower

variable {K₀ : Type u₀} [Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K]
  (E : Type uE) [Field E] [Algebra K E] [Algebra K₀ E]
  {M : Type uM} [Field M] [Algebra K₀ M]
  [Algebra K M] [Algebra E M] [IsScalarTower K E M]
  [IsScalarTower K₀ K M] [IsScalarTower K₀ E M]
  (T : LocalField.TopologicalData K₀ M)

/-- Restriction of scalars from `E` to `K` preserves the integer lower groups of one
realization: both act on `T.Integers` by the same underlying map. -/
theorem restrictScalars_mem_lowerRamificationGroupInt_iff (i : ℤ) (σ : M ≃ₐ[E] M) :
    σ.restrictScalars K ∈ lowerRamificationGroupInt T K i ↔
      σ ∈ lowerRamificationGroupInt T E i := by
  unfold lowerRamificationGroupInt lowerGroupInt
  split_ifs
  · simp
  · exact Iff.rfl

/-- The real-indexed form of `restrictScalars_mem_lowerRamificationGroupInt_iff`. -/
theorem restrictScalars_mem_lowerRamificationGroupReal_iff (t : ℝ) (σ : M ≃ₐ[E] M) :
    σ.restrictScalars K ∈ lowerRamificationGroupReal T K t ↔
      σ ∈ lowerRamificationGroupReal T E t :=
  restrictScalars_mem_lowerRamificationGroupInt_iff K E T ⌈t⌉ σ

end Lower

/-- Herbrand's finite subgroup formula `H ∩ G^u = H^{φ_{M/E}(ψ_{M/K}(u))}` at every
real `u`, for one realization of the top field in either characteristic. -/
theorem finiteHerbrandSubgroupFormula : FiniteHerbrandSubgroupFormula := by
  intro K₀ _ _ _ K _ _ E _ _ _ M _ _ _ _ _ _ _ _ T u σ
  rw [upperRamificationGroup_phi]
  exact restrictScalars_mem_lowerRamificationGroupReal_iff K E T (herbrandPsi T K u) σ

end Langlands.Ramification.Local
