import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Norm domination and intertwiners from a Hilbert sum

The norm domination argument in the remark to Jacquet–Langlands, Lemma 16.1.1, can be
expressed using two linear maps on a common test space and closure under joint translation.
-/

universe uG uι uH uE uV

namespace Langlands.TraceFormula

/-- If no summand of a Hilbert sum has a nonzero bounded intertwiner to the target,
then the Hilbert-sum norm can dominate the target norm on a jointly invariant linear
image only if its target component vanishes. -/
def HilbertSumIntertwinerDominationStatement : Prop :=
  ∀ (G : Type uG) [Group G] (ι : Type uι) (H : ι → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] (σ : (i : ι) → G →* (H i →L[ℂ] H i)),
    (∀ i g x, ‖σ i g x‖ = ‖x‖) →
    ∀ (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (π : G →* (E →L[ℂ] E)),
      (∀ (i : ι) (T : H i →L[ℂ] E), (∀ g x, T (σ i g x) = π g (T x)) → T = 0) →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (v : V →ₗ[ℂ] lp H 2) (w : V →ₗ[ℂ] E),
        (∀ g f, ∃ f', (∀ i, v f' i = σ i g (v f i)) ∧ w f' = π g (w f)) →
        (∃ C : ℝ, ∀ f, ‖w f‖ ≤ C * ‖v f‖) → w = 0

end Langlands.TraceFormula
