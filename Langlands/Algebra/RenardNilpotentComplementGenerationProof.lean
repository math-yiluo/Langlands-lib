import Langlands.Algebra.RenardNilpotentComplementGenerationStatement
import Langlands.Algebra.CommutingDimensionHelpers

/-! Generation by a complex complement to the actual first ideal-power level. -/

noncomputable section
open scoped IsMulCommutative

universe u

namespace Langlands.Renard

namespace NilpotentFiltration

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {l : ℕ} (a : Fin l → Module.End ℂ V)

/-- The complement decomposition generates every actual filtration quotient. -/
theorem idealPowerSubspace_eq_complement_succ
    (W : Submodule ℂ V) (hW : IsCompl (idealPowerSubspace a 1) W) (n : ℕ) :
    idealPowerSubspace a n =
      Submodule.span ℂ
        {v : V | ∃ (r : generatedAlgebra a) (w : W),
          r ∈ (generatorIdeal a) ^ n ∧ (r : Module.End ℂ V) (w : V) = v} ⊔
      idealPowerSubspace a (n + 1) := by
  apply le_antisymm
  · intro v hv
    change v ∈ (generatorIdeal a) ^ n • (⊤ : Submodule (generatedAlgebra a) V) at hv
    refine Submodule.smul_induction_on hv (fun r hr v _ => ?_)
      (fun x y hx hy => Submodule.add_mem _ hx hy)
    have hv : v ∈ idealPowerSubspace a 1 ⊔ W := by
      rw [hW.codisjoint.eq_top]
      trivial
    obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have hrx : r • x ∈ idealPowerSubspace a (n + 1) := by
      change x ∈ (generatorIdeal a) ^ 1 • (⊤ : Submodule (generatedAlgebra a) V) at hx
      rw [Submodule.pow_one] at hx
      refine Submodule.smul_induction_on hx (fun s hs y hy => ?_)
        (fun x y hx hy => by
          rw [smul_add]
          exact Submodule.add_mem _ hx hy)
      change r • (s • y) ∈
        (generatorIdeal a) ^ (n + 1) • (⊤ : Submodule (generatedAlgebra a) V)
      rw [← mul_smul]
      apply Submodule.smul_mem_smul _ hy
      rw [Submodule.pow_succ]
      exact Ideal.mul_mem_mul hr hs
    rw [smul_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_right hrx)
      (Submodule.mem_sup_left (Submodule.subset_span ⟨r, ⟨w, hw⟩, hr, rfl⟩))
  · refine sup_le ?_ (idealPowerSubspace_antitone a (Nat.le_succ n))
    refine Submodule.span_le.mpr ?_
    rintro v ⟨r, w, hr, rfl⟩
    change r • (w : V) ∈
      (generatorIdeal a) ^ n • (⊤ : Submodule (generatedAlgebra a) V)
    exact Submodule.smul_mem_smul hr
      (Submodule.mem_top : (w : V) ∈ (⊤ : Submodule (generatedAlgebra a) V))

end NilpotentFiltration

/-- Renard C.I: quotient generation and full generation by any such complement. -/
theorem nilpotentComplementGeneration : NilpotentComplementGenerationStatement.{u} := by
  intro V _ _ _ l a hcomm hnil W hW
  refine ⟨NilpotentFiltration.idealPowerSubspace_eq_complement_succ a W hW, ?_⟩
  let C := NilpotentFiltration.generatedAlgebra a
  let : IsMulCommutative C :=
    NilpotentFiltration.generatedAlgebra_isMulCommutative a hcomm
  have hJ : NilpotentFiltration.generatorIdeal a ≤ (⊥ : Ideal C).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hnil i
    refine ⟨k, ?_⟩
    change (NilpotentFiltration.generator a i) ^ k = 0
    apply Subtype.ext
    exact hk
  have hsup : W ⊔
      (NilpotentFiltration.generatorIdeal a • (⊤ : Submodule C V)).restrictScalars ℂ =
      ⊤ := by
    simpa only [NilpotentFiltration.idealPowerSubspace,
      NilpotentFiltration.idealPowerModule, Submodule.pow_one] using hW.symm.codisjoint.eq_top
  have hspan := Langlands.CommutingDimension.span_action_of_sup_radical_eq_top
    ℂ V C (NilpotentFiltration.generatorIdeal a) hJ W hsup
  apply top_unique
  intro v _
  have hv : v ∈ Submodule.span ℂ
      {v : V | ∃ c : C, ∃ x : W, v = c.val x} := by
    rw [hspan]
    trivial
  have hle : Submodule.span ℂ
      {v : V | ∃ c : C, ∃ x : W, v = c.val x} ≤
      (Submodule.span C (W : Set V)).restrictScalars ℂ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, x, rfl⟩
    exact (Submodule.span C (W : Set V)).smul_mem c (Submodule.subset_span x.property)
  exact hle hv

end Langlands.Renard
