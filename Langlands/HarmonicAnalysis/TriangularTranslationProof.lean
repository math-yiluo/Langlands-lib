import Langlands.HarmonicAnalysis.TriangularTranslationStatement
import Mathlib.MeasureTheory.Integral.Marginal

namespace Langlands.HarmonicAnalysis

open MeasureTheory

universe uI uX

variable {ι : Type uI} [Fintype ι] {X : ι → Type uX}
  [∀ i, AddCommGroup (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, MeasurableAdd₂ (X i)] (μ : ∀ i, Measure (X i))
  [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsAddLeftInvariant]

private theorem measurePreserving_coordinateTranslation [DecidableEq ι]
    (i : ι) (g : (∀ j, X j) → X i) (hg : Measurable g)
    (hind : ∀ (x : ∀ j, X j) (a : X i), g (Function.update x i a) = g x) :
    MeasurePreserving (fun x => Function.update x i (g x + x i))
      (Measure.pi μ) (Measure.pi μ) := by
  have ht : Measurable (fun x => Function.update x i (g x + x i)) :=
    measurable_update'.comp (measurable_id.prodMk (hg.add (measurable_pi_apply i)))
  refine ⟨ht, ?_⟩
  apply Measure.ext
  intro s hs
  simp_rw [← lintegral_indicator_one hs]
  rw [lintegral_map (measurable_one.indicator hs) ht]
  apply lintegral_eq_of_lmarginal_eq {i}
    ((measurable_one.indicator hs).comp ht) (measurable_one.indicator hs)
  simp_rw [lmarginal_singleton]
  funext x
  dsimp only [Function.comp_apply]
  simp only [hind, Function.update_self, Function.update_idem]
  exact (measurePreserving_add_left (μ i) (g x)).lintegral_comp
    ((measurable_one.indicator hs).comp (measurable_update x))

/-- A finite family of translations depending only on strictly lower ranks
preserves the product of the coordinate measures. -/
theorem measurePreserving_finiteTriangularTranslation
    (rank : ι → ℕ) (f : (∀ i, X i) → ∀ i, X i) (hf : Measurable f)
    (hdep : ∀ (i : ι) (x y : ∀ j, X j),
      (∀ j, rank j < rank i → x j = y j) → f x i = f y i) :
    MeasurePreserving (fun x i => f x i + x i) (Measure.pi μ) (Measure.pi μ) := by
  classical
  have hcoord (i : ι) :
      MeasurePreserving (fun x => Function.update x i (f x i + x i))
        (Measure.pi μ) (Measure.pi μ) := by
    apply measurePreserving_coordinateTranslation μ i (fun x => f x i)
      ((measurable_pi_apply i).comp hf)
    intro x a
    apply hdep
    intro j hj
    exact Function.update_of_ne (by intro h; subst j; exact (lt_irrefl _ hj)) _ _
  have hpartial (s : Finset ι) :
      MeasurePreserving (fun x i => if i ∈ s then f x i + x i else x i)
        (Measure.pi μ) (Measure.pi μ) := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      rcases s.eq_empty_or_nonempty with rfl | hs
      · convert MeasurePreserving.id (Measure.pi μ) using 1
        funext x i
        simp
      obtain ⟨i, hi, hmin⟩ := s.exists_min_image rank hs
      have hrest := ih (s.erase i) (Finset.erase_ssubset hi)
      have hcomp := (hcoord i).comp hrest
      convert hcomp using 1
      funext x j
      dsimp only [Function.comp_def]
      have hfi : f (fun k => if k ∈ s.erase i then f x k + x k else x k) i = f x i := by
        apply hdep
        intro k hk
        have hks : k ∉ s.erase i := by
          intro h
          exact (not_le_of_gt hk) (hmin k (Finset.mem_of_mem_erase h))
        simp only [hks, ite_false]
      rw [hfi]
      by_cases hji : j = i
      · subst j
        simp [hi]
      · simp [Finset.mem_erase, hji]
  simpa using hpartial Finset.univ

/-- The complete, universe-polymorphic published statement. -/
theorem finiteTriangularTranslation : FiniteTriangularTranslationStatement.{uI, uX} := by
  intro ι _ X _ _ _ μ _ _ rank f hf hdep
  exact measurePreserving_finiteTriangularTranslation μ rank f hf hdep

end Langlands.HarmonicAnalysis
