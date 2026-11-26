import Langlands.LinearAlgebra.FiniteRankTrace

/-! # Traces of finite block operators with finite-rank entries

For a finite index type `X`, a complex vector space `V` and finite-rank endomorphisms
`K x y` of `V`, the operator `f ↦ (x ↦ ∑ y, K x y (f y))` on `X → V` has finite rank, and its
finite-rank trace is the sum of the traces of the diagonal entries. See the paired Markdown.
-/

noncomputable section

namespace Langlands.FiniteRankEnd

universe uX uV

variable {X : Type uX} [DecidableEq X] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The linear map `ι_x ∘ T ∘ π_y` on `X → V`. -/
def blockEntryMap (x y : X) (T : Module.End ℂ V) : Module.End ℂ (X → V) :=
  (LinearMap.single ℂ (fun _ : X => V) x).comp
    (T.comp (LinearMap.proj (R := ℂ) (φ := fun _ : X => V) y))

theorem blockEntryMap_apply (x y : X) (T : Module.End ℂ V) (f : X → V) :
    blockEntryMap x y T f = Pi.single x (T (f y)) := rfl

theorem blockEntryMap_mem (x y : X) (T : finiteRankEnd V) :
    blockEntryMap x y T.val ∈ finiteRankEnd (X → V) := by
  have h : T.val.HasNoetherianRange := T.property
  exact LinearMap.mem_finiteRange_iff_hasNoetherianRange.mpr
    ((h.comp_right _).comp_left _)

/-- The single entry `ι_x ∘ T ∘ π_y` of a block operator. -/
def blockEntry (x y : X) (T : finiteRankEnd V) : finiteRankEnd (X → V) :=
  ⟨blockEntryMap x y T.val, blockEntryMap_mem x y T⟩

theorem blockEntry_apply (x y : X) (T : finiteRankEnd V) (f : X → V) :
    (blockEntry x y T).val f = Pi.single x (T.val (f y)) := rfl

/-- The trace of a single block entry is the trace of the entry on the diagonal and zero off
it. -/
theorem trace_blockEntry (x y : X) (T : finiteRankEnd V) :
    trace (blockEntry x y T) = if x = y then trace T else 0 := by
  let f : (X → V) →ₗ[ℂ] T.val.range := T.val.rangeRestrict ∘ₗ LinearMap.proj y
  let g : T.val.range →ₗ[ℂ] (X → V) :=
    LinearMap.single ℂ (fun _ : X => V) x ∘ₗ T.val.range.subtype
  have hT : (blockEntry x y T).val = g ∘ₗ f := by
    apply LinearMap.ext
    intro v
    rfl
  rw [trace_eq_of_factorization _ f g hT]
  split_ifs with hxy
  · subst hxy
    have hfg : f ∘ₗ g = onSubspace T.val T.val.range le_rfl := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      simp [f, g, onSubspace_apply]
    rw [hfg]
    rfl
  · have hfg : f ∘ₗ g = 0 := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      simp [f, g, Ne.symm hxy]
    rw [hfg, map_zero]

variable [Fintype X]

/-- The finite-rank block operator `f ↦ (x ↦ ∑ y, K x y (f y))`. -/
def blockOperator (K : X → X → finiteRankEnd V) : finiteRankEnd (X → V) :=
  ∑ x, ∑ y, blockEntry x y (K x y)

theorem blockOperator_apply (K : X → X → finiteRankEnd V) (f : X → V) (x : X) :
    (blockOperator K).val f x = ∑ y, (K x y).val (f y) := by
  simp only [blockOperator, Submodule.coe_sum, LinearMap.sum_apply, Finset.sum_apply,
    blockEntry_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_eq_single x]
  · simp
  · intro x' _ hx'
    simp [Ne.symm hx']
  · simp

/-- The trace of a block operator is the sum of the traces of its diagonal entries. -/
theorem trace_blockOperator (K : X → X → finiteRankEnd V) :
    trace (blockOperator K) = ∑ x, trace (K x x) := by
  simp only [blockOperator, map_sum, trace_blockEntry]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_ite_eq]
  simp

end Langlands.FiniteRankEnd
