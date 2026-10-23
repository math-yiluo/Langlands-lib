import Langlands.LinearAlgebra.DualTensorOneDimensionalStatement
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

noncomputable section

namespace Langlands.LinearAlgebra

universe uk ui uv uw

variable {k : Type uk} [Field k]
variable {W : Type uw} [AddCommGroup W] [Module k W]

/-- The nonzero spanning-vector formulation is precisely dimension one. -/
theorem nonzero_span_iff_finrank_one :
    (∃ w : W, w ≠ 0 ∧ ∀ w', ∃ c : k, w' = c • w) ↔
      Module.finrank k W = 1 := by
  rw [finrank_eq_one_iff']
  constructor <;> rintro ⟨w, hw, h⟩ <;> refine ⟨w, hw, ?_⟩
  · intro w'
    obtain ⟨c, hc⟩ := h w'
    exact ⟨c, hc.symm⟩
  · intro w'
    obtain ⟨c, hc⟩ := h w'
    exact ⟨c, hc.symm⟩

/-- Dimension one of a full algebraic dual reflects dimension one of its space,
without assuming finite-dimensionality in advance. -/
theorem dual_finrank_one_iff :
    Module.finrank k (Module.Dual k W) = 1 ↔ Module.finrank k W = 1 := by
  constructor
  · intro h
    have : Module.Finite k (Module.Dual k W) :=
      Module.finite_of_finrank_pos (by omega)
    have : Module.Finite k W := (Module.finite_dual_iff k).mp inferInstance
    simpa only [Subspace.dual_finrank_eq] using h
  · intro h
    have : Module.Finite k W := Module.finite_of_finrank_pos (by omega)
    simpa only [Subspace.dual_finrank_eq] using h

/-- Tensor bases prove the dimension-one criterion even for initially arbitrary
vector spaces, zero factors and the empty family. -/
theorem piTensor_finrank_one_iff {ι : Type ui} [Finite ι]
    (V : ι → Type uv) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] :
    Module.finrank k (PiTensorProduct k V) = 1 ↔
      ∀ i, Module.finrank k (V i) = 1 := by
  classical
  constructor
  · intro h
    let κ := fun i => Module.Free.ChooseBasisIndex k (V i)
    let b : ∀ i, Module.Basis (κ i) k (V i) :=
      fun i => Module.Free.chooseBasis k (V i)
    let : Unique (∀ i, κ i) :=
      Classical.choice ((Basis.piTensorProduct b).nonempty_unique_index_of_finrank_eq_one h)
    intro i
    let : Unique (κ i) :=
      { default := (default : ∀ i, κ i) i
        uniq := fun x => by
          have hx : Function.update (default : ∀ i, κ i) i x = default :=
            Subsingleton.elim _ _
          simpa only [Function.update_self] using congrFun hx i }
    simpa only [Fintype.card_unique] using Module.finrank_eq_card_basis (b i)
  · intro h
    let b : ∀ i, Module.Basis Unit k (V i) :=
      fun i => Module.basisUnique Unit (h i)
    simpa only [Fintype.card_unique] using
      Module.finrank_eq_card_basis (Basis.piTensorProduct b)

/-- Exact closed auxiliary proposition for the dimension-one step of heredity. -/
theorem dualTensorOneDimensional :
    DualTensorOneDimensionalStatement.{uk, ui, uv} := by
  intro k _ ι _ V _ _
  simp only [nonzero_span_iff_finrank_one, dual_finrank_one_iff,
    piTensor_finrank_one_iff]

end Langlands.LinearAlgebra
