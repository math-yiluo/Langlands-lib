import Langlands.LocalFactor.Abelian.ZetaConvergence

noncomputable section

open MeasureTheory Filter Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- The convergence region is open. -/
theorem isOpen_convergesAt (π : F.Carrierˣ) (χ : Character) :
    IsOpen {s : ℂ | ConvergesAt T π χ s} := by
  change IsOpen {s : ℂ | ‖(χ π : ℂ)‖ *
    Real.exp (-s.re * Real.log (T.residueCardinality : ℝ)) < 1}
  exact isOpen_lt (by fun_prop) continuous_const

/-- The convergence region contains an actual real spectral point. -/
theorem exists_convergesAt (π : F.Carrierˣ) (χ : Character) :
    ∃ s : ℂ, ConvergesAt T π χ s := by
  let r : ℝ := (Real.log ‖(χ π : ℂ)‖ + 1) /
    Real.log (T.residueCardinality : ℝ)
  have hq : 0 < Real.log (T.residueCardinality : ℝ) :=
    Real.log_pos (by exact_mod_cast T.residueCardinality_gt_one)
  have hc : 0 < ‖(χ π : ℂ)‖ := norm_pos_iff.mpr (χ π).ne_zero
  refine ⟨(r : ℂ), ?_⟩
  change ‖(χ π : ℂ)‖ *
    Real.exp (-r * Real.log (T.residueCardinality : ℝ)) < 1
  have he : ‖(χ π : ℂ)‖ *
      Real.exp (-r * Real.log (T.residueCardinality : ℝ)) = Real.exp (-1) := by
    rw [← Real.exp_log hc, ← Real.exp_add]
    congr 1
    dsimp [r]
    field_simp
    ring
  rw [he]
  exact Real.exp_lt_one_iff.mpr (by norm_num)

/-- No point of absolute convergence is an Euler pole. -/
theorem regularPoint_of_convergesAt (π : F.Carrierˣ) (χ : Character) (a : ℕ)
    (s : ℂ) (hs : ConvergesAt T π χ s) : RegularPoint T π χ a s := by
  right
  intro he
  have he' := sub_eq_zero.mp he
  have hn := (convergesAt_iff_norm_lt_one T π χ s).mp hs
  rw [← he', norm_one] at hn
  exact lt_irrefl _ hn

/-- The Euler expression is analytic at each regular point. -/
theorem analyticAt_lFactorAt_of_regular (π : F.Carrierˣ) (χ : Character)
    (a : ℕ) (s : ℂ) (hs : RegularPoint T π χ a s) :
    AnalyticAt ℂ (lFactorAt T π χ a) s := by
  classical
  by_cases ha : a = 0
  · change AnalyticAt ℂ (fun z => lFactorAt T π χ a z) s
    simp only [lFactorAt, ha, ite_true]
    exact (analyticAt_euler_denominator T π χ s).inv
      (hs.resolve_left (not_not.mpr ha))
  · change AnalyticAt ℂ (fun z => lFactorAt T π χ a z) s
    simpa only [lFactorAt, ha, ite_false] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) s)

/-- Equality on one neighborhood propagates to all punctured germs for globally meromorphic functions. -/
theorem meromorphic_germ_eq_of_eventuallyEq {Z Y : ℂ → ℂ}
    (hZ : MeromorphicOn Z Set.univ) (hY : MeromorphicOn Y Set.univ)
    {s : ℂ} (he : Z =ᶠ[𝓝 s] Y) (t : ℂ) :
    Z =ᶠ[𝓝[≠] t] Y := by
  have hm : MeromorphicOn (fun z => Z z - Y z) Set.univ := hZ.sub hY
  have hzero : (fun z => Z z - Y z) =ᶠ[𝓝[≠] s] 0 := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  have ho : meromorphicOrderAt (fun z => Z z - Y z) s = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr hzero
  have ht := hm.meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ s) (Set.mem_univ t) ho
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp ht] with z hz
  exact sub_eq_zero.mp hz

/-- Normal meromorphic representatives extending the same integral are equal. -/
theorem extendsIntegral_unique (π : F.Carrierˣ) (μ : BorelMeasure T)
    (f : F.Carrier → ℂ) (χ : Character) {Z Y : ℂ → ℂ}
    (hZ : ExtendsIntegral T π μ f χ Z) (hY : ExtendsIntegral T π μ f χ Y) :
    Z = Y := by
  obtain ⟨s, hs⟩ := exists_convergesAt T π χ
  have he : Z =ᶠ[𝓝 s] Y := by
    filter_upwards [(isOpen_convergesAt T π χ).mem_nhds hs] with z hz
    exact (hZ.2 z hz).trans (hY.2 z hz).symm
  funext t
  have hg := meromorphic_germ_eq_of_eventuallyEq hZ.1.meromorphicOn hY.1.meromorphicOn he t
  exact ((hZ.1 (Set.mem_univ t)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hY.1 (Set.mem_univ t))).mp hg |>.eq_of_nhds

/-- Every finite Laurent expression is entire as a function of the spectral parameter. -/
theorem analyticAt_laurentEvaluation (A : ℤ →₀ ℂ) (s : ℂ) :
    AnalyticAt ℂ (laurentEvaluation T A) s := by
  unfold laurentEvaluation Finsupp.sum
  exact Finset.analyticAt_fun_sum _ (fun _ _ => by fun_prop)

end Langlands.LocalFactor.PadicAbelian
