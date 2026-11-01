import Langlands.Algebra.RenardCommutativeDimensionNilpotentReductionStatement
import Langlands.Algebra.RenardCommutingGeneralizedEigenspaceDecompositionProof
import Langlands.Algebra.RenardNilpotentDimensionTransportProof
import Langlands.Algebra.RenardCommutativeDimensionPowerAssemblyProof
import Mathlib.Data.Fintype.EquivFin

/-! Renard C.I: reduction through the canonical maxima of the actual nilpotent blocks. -/

noncomputable section
open scoped BigOperators

namespace Langlands.Renard

universe u

private theorem blockDimension_le_canonicalMaximum
    (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin l → Module.End ℂ V)
    (hcomm : ∀ i j, Commute (a i) (a j)) (χ : Fin l → ℂ) :
    Module.finrank ℂ (CommutingReduction.blockAlgebra a hcomm χ) ≤
      nilpotentGeneratedPhi l
        (Module.finrank ℂ (CommutingReduction.jointSpace a χ)) := by
  have h := finrank_adjoin_le_nilpotentGeneratedMaxDimension
    l (CommutingReduction.jointSpace a χ)
    (CommutingReduction.shiftedBlockTuple a hcomm χ)
    (CommutingReduction.shiftedBlockTuple_commute a hcomm χ)
    (CommutingReduction.shiftedBlockTuple_isNilpotent a hcomm χ)
  rw [CommutingReduction.shiftedBlockTuple_adjoin_eq,
    nilpotentDimensionTransport.{u, 0}.2 l (CommutingReduction.jointSpace a χ)] at h
  exact h

private theorem powerAssembly_fintype
    (l : ℕ) (hl : 1 ≤ l) {I : Type*} [Fintype I] (x : I → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    (∑ i, Real.rpow (x i) (2 - Real.rpow 2 (1 - (l : ℝ)))) ≤
      Real.rpow (∑ i, x i) (2 - Real.rpow 2 (1 - (l : ℝ))) := by
  classical
  let e := (Fintype.equivFin I).symm
  have h := (commutativeDimensionPowerAssembly l hl).2.2
    (Fintype.card I) (fun i => x (e i)) (fun i => hx (e i))
  rw [e.sum_comp (fun i => Real.rpow (x i) (2 - Real.rpow 2 (1 - (l : ℝ)))),
    e.sum_comp x] at h
  exact h

/-- Private conditional assembly: the exact actual-block decomposition remains an input. -/
private theorem nilpotentReduction_of_jointDecomposition
    (hjoint : CommutingGeneralizedEigenspaceDecompositionStatement.{u}) :
    CommutativeDimensionNilpotentReductionStatement.{u} := by
  classical
  intro V _ _ _ l a hcomm
  have hdecomp := hjoint V l a hcomm
  have hblock := blockDimension_le_canonicalMaximum V l a hcomm
  have hsum :
      ∀ F : Fintype (CommutingReduction.jointBlockIndex a),
        letI := F
        Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) ≤
          ∑ χ : CommutingReduction.jointBlockIndex a,
            nilpotentGeneratedPhi l
              (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val)) := by
    intro F
    let := F
    exact (hdecomp.2.2.2.2.2 F).trans
      (Finset.sum_le_sum fun χ _ => hblock χ.val)
  refine ⟨hblock, hsum, ?_⟩
  intro hl
  dsimp only
  intro hbound
  let : Finite (CommutingReduction.jointBlockIndex a) := hdecomp.1
  let := Fintype.ofFinite (CommutingReduction.jointBlockIndex a)
  have hdim :
      (∑ χ : CommutingReduction.jointBlockIndex a,
        (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val) : ℝ)) =
          (Module.finrank ℂ V : ℝ) := by
    exact_mod_cast hdecomp.2.2.2.1 inferInstance
  calc
    (Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) : ℝ) ≤
        ∑ χ : CommutingReduction.jointBlockIndex a,
          (nilpotentGeneratedPhi l
            (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val)) : ℝ) := by
      exact_mod_cast hsum inferInstance
    _ ≤ ∑ χ : CommutingReduction.jointBlockIndex a,
        Real.rpow (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val) : ℝ)
          (2 - Real.rpow 2 (1 - (l : ℝ))) :=
      Finset.sum_le_sum fun χ _ => hbound χ
    _ ≤ Real.rpow
        (∑ χ : CommutingReduction.jointBlockIndex a,
          (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val) : ℝ))
        (2 - Real.rpow 2 (1 - (l : ℝ))) :=
      powerAssembly_fintype l hl _ (fun _ => Nat.cast_nonneg _)
    _ = _ := by rw [hdim]

/-- The original commuting algebra reduces to the canonical nilpotent maxima of its
actual joint blocks, with the real-power conclusion conditional on those maxima. -/
theorem commutativeDimensionNilpotentReduction :
    CommutativeDimensionNilpotentReductionStatement.{u} :=
  nilpotentReduction_of_jointDecomposition commutingGeneralizedEigenspaceDecomposition

end Langlands.Renard
