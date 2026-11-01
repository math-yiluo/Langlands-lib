import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.LinearAlgebra.Pi

/-! # Minimal generators of a local maximal ideal -/

universe u v

namespace Langlands.CommutativeAlgebra

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {ι : Type v} [Fintype ι]

/-- Independence in the cotangent space detects every coefficient of a
linear combination that belongs to the square of the maximal ideal. -/
theorem coefficients_mem_maximalIdeal_of_cotangent_independent
    (a : ι → maximalIdeal R)
    (ha : LinearIndependent (ResidueField R)
      (fun i ↦ (maximalIdeal R).toCotangent (a i)))
    (c : ι → R)
    (hc : ∑ i, c i * (a i : R) ∈ maximalIdeal R ^ 2) :
    ∀ i, c i ∈ maximalIdeal R := by
  classical
  have hz : (maximalIdeal R).toCotangent (∑ i, c i • a i) = 0 := by
    apply (Ideal.toCotangent_eq_zero _ _).mpr
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using hc
  have hsum : ∑ i, (algebraMap R (ResidueField R) (c i)) •
      (maximalIdeal R).toCotangent (a i) = 0 := by
    simpa only [map_sum, map_smul, IsScalarTower.algebraMap_smul] using hz
  intro i
  have hi := (Fintype.linearIndependent_iff.mp ha) _ hsum i
  exact Ideal.Quotient.eq_zero_iff_mem.mp hi

variable (R) [IsNoetherianRing R]

/-- Lift a cotangent-space basis to a minimal tuple of generators. The tuple is
indexed by the minimal number of generators of the maximal ideal. -/
theorem exists_minimalMaximalIdealGenerators :
    ∃ a : Fin (maximalIdeal R).spanFinrank → maximalIdeal R,
      Submodule.span R (Set.range a) = ⊤ ∧
      LinearIndependent (ResidueField R)
        (fun i ↦ (maximalIdeal R).toCotangent (a i)) := by
  classical
  let b : Module.Basis (Fin (maximalIdeal R).spanFinrank)
      (ResidueField R) (CotangentSpace R) := by
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact Module.finBasis _ _
  obtain ⟨a, ha⟩ := (maximalIdeal R).toCotangent_surjective.comp_left b
  change (maximalIdeal R).toCotangent ∘ a = b at ha
  refine ⟨a, ?_, ?_⟩
  · apply CotangentSpace.span_image_eq_top_iff.mp
    have heq : (maximalIdeal R).toCotangent '' Set.range a = Set.range b := by
      rw [← Set.range_comp, ha]
    rw [heq]
    exact b.span_eq
  · simpa only [← ha, Function.comp_def] using b.linearIndependent

/-- A chosen tuple lifting a cotangent-space basis. -/
noncomputable def minimalMaximalIdealGenerators :
    Fin (maximalIdeal R).spanFinrank → maximalIdeal R :=
  Classical.choose (exists_minimalMaximalIdealGenerators R)

theorem minimalMaximalIdealGenerators_span :
    Submodule.span R (Set.range (minimalMaximalIdealGenerators R)) = ⊤ :=
  (Classical.choose_spec (exists_minimalMaximalIdealGenerators R)).1

theorem minimalMaximalIdealGenerators_independent :
    LinearIndependent (ResidueField R)
      (fun i ↦ (maximalIdeal R).toCotangent (minimalMaximalIdealGenerators R i)) :=
  (Classical.choose_spec (exists_minimalMaximalIdealGenerators R)).2

theorem minimalMaximalIdealGenerators_coefficients
    (c : Fin (maximalIdeal R).spanFinrank → R)
    (hc : ∑ i, c i * (minimalMaximalIdealGenerators R i : R) ∈ maximalIdeal R ^ 2) :
    ∀ i, c i ∈ maximalIdeal R :=
  coefficients_mem_maximalIdeal_of_cotangent_independent
    (minimalMaximalIdealGenerators R) (minimalMaximalIdealGenerators_independent R) c hc

end Langlands.CommutativeAlgebra
