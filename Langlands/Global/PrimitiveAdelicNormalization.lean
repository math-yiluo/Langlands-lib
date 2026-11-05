import Langlands.Global.PrimitiveAdelicContent
import Langlands.Global.NormOneIdeleClassCompact

/-! # Compact normalization of actual primitive adelic vectors -/

noncomputable section

universe u

open scoped NNReal Topology Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Actual adelic vectors with maximum coordinate norm one at every place. -/
def normalizedSet : Set (Vector F n) :=
  {x | (∀ v : FinitePlace F, finiteNorm F n x v = 1) ∧
    ∀ v : InfinitePlace F, infiniteNorm F n x v = 1}

/-- The finite local maximum norm is continuous on the actual vector space. -/
theorem continuous_finiteNorm (v : FinitePlace F) : Continuous (fun x : Vector F n =>
    finiteNorm F n x v) :=
  (continuous_pi fun i => (continuous_finiteProjection F v).comp (continuous_apply i)).norm

/-- The infinite local maximum norm is continuous on the actual vector space. -/
theorem continuous_infiniteNorm (v : InfinitePlace F) : Continuous (fun x : Vector F n =>
    infiniteNorm F n x v) :=
  (continuous_pi fun i => (continuous_infiniteProjection F v).comp (continuous_apply i)).norm

/-- Normalized vectors form a closed subset of the actual vector space. -/
theorem isClosed_normalizedSet : IsClosed (normalizedSet F n) := by
  simp only [normalizedSet, Set.ofPred_and, ← Set.iInter_ofPred]
  exact (isClosed_iInter fun v => isClosed_eq (continuous_finiteNorm F n v) continuous_const).inter
    (isClosed_iInter fun v => isClosed_eq (continuous_infiniteNorm F n v) continuous_const)

private theorem normalizedSet_subset_adeleBox :
    normalizedSet F n ⊆ Set.univ.pi (fun _ : Fin n => NormOneIdeleClass.adeleBox F 1) := by
  intro x hx i _
  constructor
  · intro v
    exact (norm_le_pi_norm (fun j : Fin n => infiniteProjection F v (x j)) i).trans_eq (hx.2 v)
  · rw [mem_integralFiniteAdeles]
    intro v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    exact (norm_le_pi_norm (fun j : Fin n => finiteProjection F v (x j)) i).trans_eq (hx.1 v)

/-- The set of vectors with local maximum norms one is compact in the actual
full adelic vector topology. -/
theorem isCompact_normalizedSet : IsCompact (normalizedSet F n) :=
  (isCompact_univ_pi fun _ : Fin n => NormOneIdeleClass.isCompact_adeleBox F 1).of_isClosed_subset
    (isClosed_normalizedSet F n) (normalizedSet_subset_adeleBox F n)

/-- The chosen normalization belongs to the fixed compact normalized set. -/
theorem normalizedVector_mem (x : Vector F n) (hx : IsPrimitive F n x) :
    normalizedVector F n x hx ∈ normalizedSet F n :=
  ⟨finiteNorm_normalizedVector F n x hx, infiniteNorm_normalizedVector F n x hx⟩

/-- Every primitive vector is a scalar idele times a vector in the same compact
normalized set; the idele norm equals its original positive height. -/
theorem exists_content_mul_normalized (x : Vector F n) (hx : IsPrimitive F n x) :
    ∃ (t : Ideles F) (y : Vector F n), y ∈ normalizedSet F n ∧
      x = t.val • y ∧ IdeleAbsoluteValue.full F t = positiveHeight F n x hx :=
  ⟨contentIdele F n x hx, normalizedVector F n x hx, normalizedVector_mem F n x hx,
    (contentIdele_smul_normalizedVector F n x hx).symm, full_contentIdele F n x hx⟩

end Langlands.Global.PrimitiveAdelicHeight
