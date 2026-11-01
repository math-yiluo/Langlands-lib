import Langlands.Algebra.RenardNilpotentHeadTailDimensionStatement
import Langlands.Algebra.RenardNilpotentDimensionTransportProof

/-! The actual head/tail splitting and first-level dimension estimates in Renard C.I. -/

noncomputable section
open scoped IsMulCommutative

universe u

namespace Langlands.Renard

open NilpotentFiltration

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

private theorem headIdealSubspace_eq_mulLeft_range {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V)
    [IsMulCommutative (generatedAlgebra a)] :
    headIdealSubspace a = LinearMap.range (LinearMap.mulLeft ℂ (generator a 0)) := by
  ext r
  change r ∈ Ideal.span {generator a 0} ↔ _
  rw [Ideal.mem_span_singleton', LinearMap.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (mul_comm _ _).trans hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (mul_comm _ _).trans hc⟩

private theorem tail_sup_head_eq_top {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V)
    [IsMulCommutative (generatedAlgebra a)] :
    (tailAlgebra a).toSubmodule ⊔ headIdealSubspace a = ⊤ := by
  let U := (tailAlgebra a).toSubmodule ⊔ headIdealSubspace a
  have hone : (1 : generatedAlgebra a) ∈ U :=
    Submodule.mem_sup_left (tailAlgebra a).one_mem
  have hmul : ∀ x y : generatedAlgebra a, x ∈ U → y ∈ U → x * y ∈ U := by
    intro x y hx hy
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hy
    refine Submodule.mem_sup.mpr ⟨b * d, (tailAlgebra a).mul_mem hb hd,
      b * e + d * c + c * e, ?_, ?_⟩
    · exact (headIdeal a).add_mem
        ((headIdeal a).add_mem ((headIdeal a).mul_mem_left b he)
          ((headIdeal a).mul_mem_left d hc))
        ((headIdeal a).mul_mem_left c he)
    · ring
  let A : Subalgebra ℂ (generatedAlgebra a) := U.toSubalgebra hone hmul
  have htop : (⊤ : Subalgebra ℂ (generatedAlgebra a)) ≤ A := by
    have hgen : Algebra.adjoin ℂ (Set.range (generator a)) =
        (⊤ : Subalgebra ℂ (generatedAlgebra a)) :=
      Langlands.CommutingDimension.adjoin_generators_top ℂ a
    have hheadtail : Algebra.adjoin ℂ
        (insert (generator a 0) (tailAlgebra a : Set (generatedAlgebra a))) = ⊤ :=
      Langlands.CommutingDimension.adjoin_head_tail ℂ (generator a) hgen
    rw [← hheadtail]
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with rfl | hx
    · exact Submodule.mem_sup_right (generator_zero_mem_headIdeal a)
    · exact Submodule.mem_sup_left hx
  exact top_unique fun x hx => htop hx

/-- Renard's five comparisons for each original commuting nilpotent tuple. -/
theorem nilpotentHeadTailDimension : NilpotentHeadTailDimensionStatement.{u} := by
  intro V _ _ _ l a hcomm hnil
  let : IsMulCommutative (generatedAlgebra a) :=
    generatedAlgebra_isMulCommutative a hcomm
  have hsplit := tail_sup_head_eq_top a
  have htaildim : Module.finrank ℂ (tailAlgebra a) =
      Module.finrank ℂ (generatedAlgebra (Fin.tail a)) := by
    have h := ((tailAlgebra a).equivMapOfInjective (generatedAlgebra a).val
      Subtype.val_injective).toLinearEquiv.finrank_eq
    rwa [tailAlgebra_map] at h
  have htail : Module.finrank ℂ (tailAlgebra a) ≤
      nilpotentGeneratedPhi l (Module.finrank ℂ V) := by
    rw [htaildim]
    exact (finrank_adjoin_le_nilpotentGeneratedMaxDimension l V (Fin.tail a)
      (fun i j => hcomm i.succ j.succ) (fun i => hnil i.succ)).trans_eq
      (nilpotentDimensionTransport.{u, 0}.2 l V)
  have hhead : Module.finrank ℂ (headIdealSubspace a) ≤
      Module.finrank ℂ (firstLevelAlgebra a) := by
    rw [headIdealSubspace_eq_mulLeft_range, firstLevelAlgebra_eq_range]
    exact Langlands.CommutingDimension.multiplication_dimension_le_restriction
      ℂ V (generatedAlgebra a)
      (fun c d => congrArg Subtype.val (mul_comm c d))
      (generator a 0) (idealPowerSubspace a 1)
      (fun r _ hv => idealPowerSubspace_stable a 1 r hv)
      (generator_apply_mem_one a 0)
  have hfirst : Module.finrank ℂ (firstLevelAlgebra a) ≤
      nilpotentGeneratedPhi (l + 1) (Module.finrank ℂ (idealPowerSubspace a 1)) :=
    (finrank_adjoin_le_nilpotentGeneratedMaxDimension (l + 1)
      (idealPowerSubspace a 1) (firstLevelTuple a)
      (firstLevelTuple_commute a hcomm) (firstLevelTuple_isNilpotent a hnil)).trans_eq
      (nilpotentDimensionTransport.{u, 0}.2 (l + 1) (idealPowerSubspace a 1))
  refine ⟨hsplit, htail, hhead, hfirst, ?_⟩
  intro W hW
  have hdim := Submodule.finrank_add_le_finrank_add_finrank
    (tailAlgebra a).toSubmodule (headIdealSubspace a)
  rw [hsplit, finrank_top] at hdim
  have hcodim : Module.finrank ℂ (idealPowerSubspace a 1) =
      Module.finrank ℂ V - Module.finrank ℂ W := by
    have h := Submodule.finrank_add_eq_of_isCompl hW
    omega
  calc
    Module.finrank ℂ (generatedAlgebra a) ≤
        Module.finrank ℂ (tailAlgebra a) + Module.finrank ℂ (headIdealSubspace a) := hdim
    _ ≤ nilpotentGeneratedPhi l (Module.finrank ℂ V) +
        nilpotentGeneratedPhi (l + 1) (Module.finrank ℂ (idealPowerSubspace a 1)) :=
      Nat.add_le_add htail (hhead.trans hfirst)
    _ = _ := by rw [hcodim]

end Langlands.Renard
