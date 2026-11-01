import Langlands.Algebra.RenardCommutingGeneralizedEigenspaceDecompositionStatement
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Decomposition and restriction dimensions for the original joint generalized eigenspaces. -/

noncomputable section
open scoped BigOperators

namespace Langlands.Renard

universe u

/-- The actual joint decomposition detects the original algebra and bounds its dimension
by the sum of the actual block-algebra dimensions. -/
theorem commutingGeneralizedEigenspaceDecomposition :
    CommutingGeneralizedEigenspaceDecompositionStatement.{u} := by
  classical
  intro V _ _ _ l a hcomm
  have hind : iSupIndep (CommutingReduction.jointSpace a) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo a
      (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ)
  have htop : (⨆ χ, CommutingReduction.jointSpace a χ) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      a (fun i j _ => hcomm i j) (fun i => (a i).iSup_maxGenEigenspace_eq_top)
  have hfinite : Finite (CommutingReduction.jointBlockIndex a) := by
    let : Fintype (CommutingReduction.jointBlockIndex a) :=
      hind.fintypeNeBotOfFiniteDimensional
    infer_instance
  have hspan : (⨆ χ : CommutingReduction.jointBlockIndex a,
      CommutingReduction.jointSpace a χ.val) = ⊤ := by
    apply top_unique
    rw [← htop]
    apply iSup_le
    intro χ
    by_cases hχ : CommutingReduction.jointSpace a χ = ⊥
    · rw [hχ]
      exact bot_le
    · exact le_iSup (fun χ : CommutingReduction.jointBlockIndex a =>
        CommutingReduction.jointSpace a χ.val) ⟨χ, hχ⟩
  refine ⟨hfinite, hind, hspan, ?_, ?_, ?_⟩
  · intro F
    let := F
    have h := ((hind.comp Subtype.val_injective).linearEquiv hspan).finrank_eq
    rw [← Module.finrank_directSum (R := ℂ)
      (fun χ : CommutingReduction.jointBlockIndex a =>
        CommutingReduction.jointSpace a χ.val)]
    exact h
  · intro r s hrs
    have hker : (⊤ : Submodule ℂ V) ≤
        ((r : Module.End ℂ V) - (s : Module.End ℂ V)).ker := by
      rw [← hspan]
      apply iSup_le
      intro χ v hv
      have heq := congrArg Subtype.val (LinearMap.congr_fun (congrFun hrs χ) ⟨v, hv⟩)
      change (r : Module.End ℂ V) v - (s : Module.End ℂ V) v = 0
      exact sub_eq_zero.mpr heq
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact sub_eq_zero.mp (hker Submodule.mem_top)
  · intro F
    let := F
    have h := Langlands.CommutingDimension.dimension_le_sum_restrictions ℂ V
      (NilpotentFiltration.generatedAlgebra a)
      (fun χ : CommutingReduction.jointBlockIndex a =>
        CommutingReduction.jointSpace a χ.val)
      (fun χ => CommutingReduction.jointSpace_stable a hcomm χ.val) hspan
    refine h.trans_eq (Finset.sum_congr rfl ?_)
    intro χ _
    exact congrArg (fun B : Subalgebra ℂ
      (Module.End ℂ (CommutingReduction.jointSpace a χ.val)) => Module.finrank ℂ B)
      (CommutingReduction.blockAlgebra_eq_range a hcomm χ.val).symm

end Langlands.Renard
