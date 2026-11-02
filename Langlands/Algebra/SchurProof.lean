import Langlands.Algebra.SchurStatements
import Langlands.Algebra.AmitsurProof

/-!
# Renard B.II: proof of Schur's lemma, unital core

Proofs of the propositions of `Langlands.Algebra.SchurStatements` (Renard,
*Représentations des groupes réductifs p-adiques*, 2026, Appendix B.II, printed page 272).
A nonzero endomorphism of a simple module is bijective (Mathlib's
`LinearMap.bijective_of_ne_zero`), hence a unit, so `Module.End A M` is a division ring.
For `m ≠ 0` the action map `a ↦ a • m` is surjective, which bounds the rank of `M` by that
of `A`, and evaluation `f ↦ f m` is injective, which bounds the rank of `Module.End A M` by
that of `M`. Amitsur's theorem `amitsurDivisionAlgebra` (B.I) applied to the division
algebra `Module.End A M` then makes `algebraMap ℂ (Module.End A M)` bijective.
-/

universe u v

namespace Langlands.Renard

/-- **Renard B.II, first step of the proof.** A nonzero endomorphism of a simple unital
module is bijective. -/
theorem schurEndBijective (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module A M] : SchurEndBijectiveStatement A M := by
  intro _ f hf
  exact LinearMap.bijective_of_ne_zero hf

/-- **Renard B.II, Théorème a).** The endomorphism ring of a simple unital module is
nontrivial and every nonzero endomorphism is a unit. -/
theorem schurEndDivision (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module A M] : SchurEndDivisionStatement A M := by
  intro hS
  have := IsSimpleModule.nontrivial A M
  exact ⟨inferInstance, fun f hf => (Module.End.isUnit_iff f).2 (schurEndBijective A M hS f hf)⟩

/-- **Renard B.II, proof.** For a nonzero vector `m` of a simple unital module, the
complex-linear action map `a ↦ a • m` is surjective. -/
theorem schurCyclicMapSurjective (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurCyclicMapSurjectiveStatement A M := by
  intro _ m hm
  exact IsSimpleModule.toSpanSingleton_surjective A hm

/-- **Renard B.II, proof of b).** For a nonzero vector `m` of a simple unital module, the
complex-linear evaluation map `f ↦ f m` on `Module.End A M` is injective. -/
theorem schurEvaluationInjective (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurEvaluationInjectiveStatement A M := by
  intro _ m hm
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  by_contra hne
  exact hm (LinearMap.injective_of_ne_zero hne (hf.trans f.map_zero.symm))

/-- **Renard B.II, proof of the final sentence.** If `A` has at most countable complex
dimension, so does a simple unital `A`-module with compatible complex structure: the
surjective action map at a nonzero vector bounds the rank of `M` by that of `A`. -/
theorem schurModuleRankCountable (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] : SchurModuleRankCountableStatement A M := by
  intro _ hS hA
  have := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have h := LinearMap.lift_rank_le_of_surjective _ (schurCyclicMapSurjective A M hS m hm)
  rw [← Cardinal.lift_le_aleph0.{v, u}]
  exact h.trans (Cardinal.lift_le_aleph0.2 hA)

/-- **Renard B.II, proof of b).** If a simple unital module has at most countable complex
dimension, so does its endomorphism algebra: evaluation at a nonzero vector is an injective
complex-linear map `Module.End A M → M`. -/
theorem schurEndRankCountable (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurEndRankCountableStatement A M := by
  intro hS hM
  have := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  exact (LinearMap.rank_le_of_injective _ (schurEvaluationInjective A M hS m hm)).trans hM

/-- **Renard B.II, Théorème b).** If a simple unital module has at most countable complex
dimension, `algebraMap ℂ (Module.End A M)` is bijective: `Module.End A M` is a division
algebra of at most countable dimension, to which Amitsur's theorem applies. -/
theorem schurScalarOfModuleRankCountable (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurScalarOfModuleRankCountableStatement A M := by
  intro hS hM
  classical
  exact amitsurDivisionAlgebra (Module.End A M) (schurEndRankCountable A M hS hM)

/-- **Renard B.II, Théorème b), final sentence.** At most countable complex dimension of
`A` suffices for `algebraMap ℂ (Module.End A M)` to be bijective. -/
theorem schurScalarOfAlgebraRankCountable (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurScalarOfAlgebraRankCountableStatement A M := fun hS hA =>
  schurScalarOfModuleRankCountable A M hS (schurModuleRankCountable A M inferInstance hS hA)

/-- **Renard B.II, Théorème, unital core.** Parts a) and b), with both countability
alternatives of b). -/
theorem schurTheorem (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v) [AddCommGroup M]
    [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] : SchurTheoremStatement A M :=
  ⟨schurEndDivision A M, schurScalarOfModuleRankCountable A M,
    schurScalarOfAlgebraRankCountable A M⟩

end Langlands.Renard
