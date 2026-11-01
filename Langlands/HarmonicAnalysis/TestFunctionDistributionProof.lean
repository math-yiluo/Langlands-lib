import Langlands.HarmonicAnalysis.TestFunctionDistributionStatements
import Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
import Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Renard II.1.2: disjoint indicators and both exact sequences -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u

namespace Langlands.HarmonicAnalysis.TestFunctionDistributionProof

open TestFunctionDistributionStatements
open Hecke.TestFunction

/-- The finitely many nonzero fibers are already disjoint compact clopen sets. -/
theorem disjointIndicatorDecomposition : DisjointIndicatorDecomposition.{u} := by
  classical
  intro X _ _ _ _ f
  let S : Set ℂ := {c | c ∈ Set.range f ∧ c ≠ 0}
  have hS : S.Finite :=
    (finite_range_of_locallyConstant_of_hasCompactSupport
      f.locallyConstant f.hasCompactSupport).subset (fun _ hc => hc.1)
  let : Fintype S := hS.fintype
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let V (i : Fin (Fintype.card S)) : Set X := {x | f x = (e i).val}
  have hVo (i) : IsClopen (V i) := f.locallyConstant.isClopen_fiber (e i).val
  have hVc (i) : IsCompact (V i) := isCompact_fiber f (e i).property.2
  refine ⟨Fintype.card S, V, hVo, hVc, fun i => (e i).val, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (e.injective (Subtype.ext (hxi.symm.trans hxj)))
  · apply Hecke.TestFunction.ext
    intro x
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    symm
    by_cases hx : f x = 0
    · have hnot (i) : x ∉ V i := by
        intro hi
        exact (e i).property.2 (hi.symm.trans hx)
      simp [characteristic_apply, Set.indicator_of_notMem, hnot, hx]
    · let c : S := ⟨f x, ⟨⟨x, rfl⟩, hx⟩⟩
      let i : Fin (Fintype.card S) := e.symm c
      have hei : e i = c := e.apply_symm_apply c
      rw [Finset.sum_eq_single i]
      · have hmem : x ∈ V i := by
          change f x = (e i).val
          rw [hei]
        simp [characteristic_apply, Set.indicator_of_mem hmem, hei, c]
      · intro j _ hji
        have hnot : x ∉ V j := by
          intro hj
          have hej : e j = c := Subtype.ext hj.symm
          exact hji (e.injective (hej.trans hei.symm))
        simp [characteristic_apply, Set.indicator_of_notMem hnot]
      · simp

/-- Exactness uses the existing pointwise zero-extension laws and closed extension. -/
theorem testFunctionExactSequence : TestFunctionExactSequence.{u} := by
  intro X _ _ _ _ U hU
  refine ⟨SchwartzBruhat.extendZero_injective hU, ?_,
    SchwartzBruhat.closedRestrictionSurjective X Uᶜ hU.isClosed_compl⟩
  apply Submodule.ext
  intro f
  constructor
  · rintro ⟨g, rfl⟩
    apply LinearMap.mem_ker.mpr
    ext z
    exact SchwartzBruhat.extendZero_apply_of_not_mem hU g z.property
  · intro hf
    apply Distribution.FiniteOrbitVanishingProof.exists_extension_eq
      (SchwartzBruhat.extendZero hU)
      (SchwartzBruhat.extendZero_apply_subtype hU)
      (fun g x hx => SchwartzBruhat.extendZero_apply_of_not_mem hU g hx) f
    intro x hx
    exact congrArg (fun g : SchwartzBruhat ↥(Uᶜ : Set X) => g ⟨x, hx⟩)
      (LinearMap.mem_ker.mp hf)

/-- Algebraic duality reverses the complete test-function exact sequence. -/
theorem distributionExactSequence : DistributionExactSequence.{u} := by
  intro X _ _ _ _ U hU
  obtain ⟨hinj, hmiddle, hsurj⟩ := testFunctionExactSequence X U hU
  refine ⟨LinearMap.dualMap_injective_of_surjective hsurj, ?_,
    LinearMap.dualMap_surjective_of_injective hinj⟩
  change LinearMap.range (SchwartzBruhat.restrictClosed hU.isClosed_compl).dualMap =
    LinearMap.ker (SchwartzBruhat.extendZero hU).dualMap
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, hmiddle]

/-- The exact unchanged scalar indicator and open-closed sequence target. -/
theorem assertions : Assertions.{u} :=
  ⟨disjointIndicatorDecomposition, testFunctionExactSequence, distributionExactSequence⟩

end Langlands.HarmonicAnalysis.TestFunctionDistributionProof
