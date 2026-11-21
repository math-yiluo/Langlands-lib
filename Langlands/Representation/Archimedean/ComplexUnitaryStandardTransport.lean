import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Langlands.Representation.Archimedean.ComplexStandardPermutationProof
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-! Pullback of infinitesimal unitarity to the compact-finite complex principal series. -/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

universe uV

variable {n : ℕ} {ds : List ComplexCharacterData} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- An injective intertwiner carries infinitesimal unitarity back to the standard module. -/
theorem isComplexUnitarizableGKModule_standard_of_injective
    {A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V}
    (hA : IsComplexStandardIntertwining n ρ π ds A) (hinj : Function.Injective A)
    (hU : IsComplexUnitarizableGKModule n ρ π) :
    IsComplexUnitarizableGKModule n (complexStandardRep n ds) (complexStandardLie n ds) := by
  obtain ⟨b, hb⟩ := hU
  let T : (complexStandardRep n ds).IntertwiningMap ρ :=
    { toLinearMap := A
      isIntertwining' := fun k => LinearMap.ext (hA.map_rep k) }
  refine ⟨b.comap T hinj, fun X v w => ?_⟩
  change b.inner (A (complexStandardLie n ds (1 ⊗ₜ X) v)) (A w) +
    b.inner (A v) (A (complexStandardLie n ds (1 ⊗ₜ X) w)) = 0
  rw [hA.map_lie, hA.map_lie]
  exact hb X (A v) (A w)

/-- An irreducible unitarizable module with a standard parameter gives an irreducible
unitarizable standard module for every permutation of that parameter. -/
theorem complexStandard_irreducible_unitarizable_of_parameter
    (hirr : IsIrreducibleGKModule ρ π) (hU : IsComplexUnitarizableGKModule n ρ π)
    (hds : HasComplexStandardParameter n ρ π ds) {cs : List ComplexCharacterData}
    (hcs : cs.Perm ds) :
    IsIrreducibleGKModule (complexStandardRep n cs) (complexStandardLie n cs) ∧
    IsComplexUnitarizableGKModule n (complexStandardRep n cs) (complexStandardLie n cs) := by
  obtain ⟨hn, A, hinj, hA⟩ := (hasComplexStandardParameter_iff n ρ π ds).mp hds
  have hIR := isIrreducibleGKModule_of_injective hirr hA hinj (complexStandardNontrivial n ds hn)
  obtain ⟨S, hSbij, hS⟩ := complexStandardPermutation n ds cs hn hcs hIR
  have hSA := hS.comp A hA.map_rep (fun X => hA.map_lie (1 ⊗ₜ X))
  have hinjSA := hinj.comp hSbij.injective
  exact ⟨isIrreducibleGKModule_of_injective hirr hSA hinjSA
      (complexStandardNontrivial n cs (hcs.length_eq.trans hn)),
    isComplexUnitarizableGKModule_standard_of_injective hSA hinjSA hU⟩

end Langlands.Archimedean
