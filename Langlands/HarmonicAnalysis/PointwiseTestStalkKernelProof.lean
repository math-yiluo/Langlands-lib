import Langlands.HarmonicAnalysis.PointwiseTestStalkKernelStatement
import Langlands.Sheaf.Renard.ProjectorStalkProof

/-! # The original-module stalk kernel and its vanishing-test generators -/

noncomputable section

open Langlands.Algebra Langlands.Sheaf.Renard
open Langlands.Sheaf.Renard.ProjectorBasisSheaf
open TopologicalSpace

universe uX uM

namespace Langlands.HarmonicAnalysis.PointwiseTestModule

open PointwiseTestAlgebra

/-- The two exact stalk-kernel comparisons at independent space and module universes. -/
theorem nondegenerateStalkKernel : NondegenerateStalkKernelStatement.{uX, uM} := by
  intro X _ hX M _ _ hM x m
  let _ := ProjectorVectorSheaf.originalModule hM
  have hfirst :
      (∃ f : Carrier X, f x ≠ 0 ∧ f • m = 0) ↔
        ∃ (U : Set X) (hU : IsClopen U) (hc : IsCompact U),
          x ∈ U ∧ characteristic hU hc • m = 0 := by
    have h := ProjectorStalk.annihilatorDescription hX hM x m
    rw [ProjectorStalk.mem_annihilatorSubmodule] at h
    constructor
    · intro hm
      obtain ⟨U, hxU, hUm⟩ := h.mp hm
      refine ⟨U.obj, clopen hX U, compact hX U, hxU, ?_⟩
      rw [map_zero] at hUm
      exact hUm
    · rintro ⟨U, hU, hc, hxU, hUm⟩
      apply h.mpr
      let V : CompactOpen hX := ⟨⟨U, hU.isOpen⟩, hc⟩
      refine ⟨V, hxU, ?_⟩
      change characteristic hU hc • m = characteristic hU hc • (0 : M)
      rw [hUm, smul_zero]
  refine ⟨hfirst, ⟨?_, ?_⟩⟩
  · intro hm
    obtain ⟨U, hU, hcU, hxU, hUm⟩ := hfirst.mp hm
    obtain ⟨V, hV, hcV, hVm⟩ := exists_characteristic_fixer hM m
    let a : Carrier X := characteristic hU hcU
    let e : Carrier X := characteristic hV hcV
    let g : Carrier X := e - a * e
    have hgx : g x = 0 := by
      change e x - a x * e x = 0
      simp [a, hxU]
    have hgm : g • m = m := by
      have hsub : g • m = e • m - (a * e) • m :=
        DFunLike.congr_fun
          (map_sub (NonUnitalModule.toEndHom
            (inferInstance : NonUnitalModule (Carrier X) M)) e (a * e)) m
      have hmul : (a * e) • m = a • (e • m) :=
        NonUnitalModuleCorner.originalAction_mul a e m
      rw [hsub, hmul, hVm, hUm, sub_zero]
    exact AddSubgroup.subset_closure ⟨g, m, hgx, hgm⟩
  · intro hm
    let K : AddSubgroup M := (ProjectorStalk.annihilatorSubmodule hX hM x).toAddSubgroup
    have hgen :
        {y : M | ∃ (f : Carrier X) (m' : M), f x = 0 ∧ f • m' = y} ⊆ K := by
      rintro y ⟨f, m', hfx, rfl⟩
      change ∃ g : Carrier X, g x ≠ 0 ∧ g • (f • m') = 0
      let V : Opens X :=
        ⟨{z | f z = f x}, (locallyConstant f).isOpen_fiber _⟩
      obtain ⟨U, hxU, hUV⟩ := (compactOpenBasis hX).exists_subset V (x := x) rfl
      refine ⟨test hX U, ?_, ?_⟩
      · simp [test, characteristic_apply, hxU]
      · have hmul : test hX U * f = 0 := by
          ext z
          by_cases hz : z ∈ U.obj
          · have hfz : f z = f x := hUV hz
            simp [test, characteristic_apply, hz, hfz, hfx]
          · simp [test, characteristic_apply, hz]
        change NonUnitalModuleCorner.originalAction (test hX U)
          (NonUnitalModuleCorner.originalAction f m') = 0
        rw [← NonUnitalModuleCorner.originalAction_mul, hmul,
          NonUnitalModuleCorner.originalAction_zero]
    exact ((AddSubgroup.closure_le K).mpr hgen) hm

end Langlands.HarmonicAnalysis.PointwiseTestModule
