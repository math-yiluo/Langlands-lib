import Langlands.Global.Factors.GermRationalComparisonStatement

noncomputable section

set_option autoImplicit false

open Filter Topology

namespace Langlands.Global.FunctionalEquationComparison

theorem germRationalComparison : GermRationalComparisonStatement := by
  intro q hq f g R S hR hS heq
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hS
  let c : ℝ := max a b + 1
  have hac : a < c := by dsimp [c]; linarith [le_max_left a b]
  have hbc : b < c := by dsimp [c]; linarith [le_max_right a b]
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (heq (c : ℂ))
  let I : Set ℝ := Set.Ioo c (c + δ)
  have hI : I.Infinite := Set.Ioo_infinite (by linarith)
  let U : Set ℂ := (fun t : ℝ => RankinSelberg.spectralPoint q (t : ℂ)) '' I
  have hU : U.Infinite :=
    hI.image (RankinSelberg.spectralPoint_ofReal_injective hq).injOn
  have hfg : ∀ t ∈ I, f (t : ℂ) = g (t : ℂ) := by
    intro t ht
    apply hball
    refine ⟨?_, ?_⟩
    · change dist (t : ℂ) (c : ℂ) < δ
      rw [Complex.isometry_ofReal.dist_eq]
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2]
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj]
        using ne_of_gt ht.1
  apply RankinSelberg.rationalFunction_eq_of_infinite_eval_eq R S U hU
  · rintro x ⟨t, ht, rfl⟩
    exact (ha (t : ℂ) (hac.trans ht.1)).1
  · rintro x ⟨t, ht, rfl⟩
    exact (hb (t : ℂ) (hbc.trans ht.1)).1
  · rintro x ⟨t, ht, rfl⟩
    exact (ha (t : ℂ) (hac.trans ht.1)).2.symm.trans
      ((hfg t ht).trans (hb (t : ℂ) (hbc.trans ht.1)).2)

end Langlands.Global.FunctionalEquationComparison
