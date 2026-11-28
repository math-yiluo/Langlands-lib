import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialChart
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Injectivity of exponential coordinates on conjugation domains -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Filter Metric Set _root_.Topology

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F]

omit [CharZero F] in
private theorem exists_pos_nat_norm_lt_one [ProperSpace F] :
    ∃ p : ℕ, p ≠ 0 ∧ ‖(p : F)‖ < 1 := by
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : F) 1).totallyBounded (1 / 2) (by norm_num)
  have hcenter (n : ℕ) : ∃ c : t, dist (n : F) (c : F) < 1 / 2 := by
    have hn : (n : F) ∈ closedBall 0 1 := by
      simpa only [mem_closedBall, dist_zero_right] using IsUltrametricDist.norm_natCast_le_one F n
    obtain ⟨c, hc, hnc⟩ := mem_iUnion₂.mp (hcover hn)
    exact ⟨⟨c, hc⟩, hnc⟩
  choose f hf using hcenter
  let : Finite t := ht
  obtain ⟨a, b, hab, hfEq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hdist : dist (a : F) (b : F) < 1 := by
    have ha := hf a
    have hb := hf b
    rw [← hfEq, dist_comm (b : F)] at hb
    have h := dist_triangle (a : F) (f a : F) (b : F)
    linarith
  have hdiff {m n : ℕ} (hmn : m < n) (h : dist (n : F) (m : F) < 1) :
      ∃ p : ℕ, p ≠ 0 ∧ ‖(p : F)‖ < 1 := by
    refine ⟨n - m, (Nat.sub_pos_of_lt hmn).ne', ?_⟩
    rwa [Nat.cast_sub hmn.le, ← dist_eq_norm]
  rcases lt_or_gt_of_ne hab with h | h
  · exact hdiff h (by simpa only [dist_comm] using hdist)
  · exact hdiff h hdist

variable {A : Type*} [NormedRing A] [NormedAlgebra F A] [CompleteSpace A]

/-- The exponential of a natural multiple of an argument in the convergence ball
is the corresponding power of its exponential. -/
theorem exp_nat_smul_of_mem_eball {x : A}
    (hx : x ∈ eball 0 (NormedSpace.expSeries F A).radius) (n : ℕ) :
    NormedSpace.exp (n • x) = NormedSpace.exp x ^ n := by
  have hn (m : ℕ) : m • x ∈ eball 0 (NormedSpace.expSeries F A).radius := by
    rw [mem_eball, edist_dist, dist_zero_right] at hx ⊢
    refine (ENNReal.ofReal_le_ofReal ?_).trans_lt hx
    rw [← Nat.cast_smul_eq_nsmul F]
    exact (norm_smul_le _ _).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one F m) (norm_nonneg x))
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : Commute (n • x) x := by
      rw [← Nat.cast_smul_eq_nsmul F]
      change ((n : F) • x) * x = x * ((n : F) • x)
      rw [smul_mul_assoc, mul_smul_comm]
    rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball hc (hn n) hx, ih, pow_succ]

/-- On the saturation of its convergence ball by algebra automorphisms, exponential
coordinates are injective, regardless of the norms of the automorphisms. -/
def ExponentialConjugacyStatement (F A : Type*) [NontriviallyNormedField F]
    [IsUltrametricDist F] [CharZero F] [ProperSpace F] [NormedRing A] [NormedAlgebra F A]
    [CompleteSpace A] [FiniteDimensional F A] : Prop :=
  Set.InjOn (fun x : A => NormedSpace.exp x)
    {z | ∃ e : A ≃ₐ[F] A, ∃ x ∈ eball 0 (NormedSpace.expSeries F A).radius, e x = z}

variable [ProperSpace F] [FiniteDimensional F A]

omit [IsUltrametricDist F] [CompleteSpace A] in
private theorem map_exp (e : A ≃ₐ[F] A) (z : A) :
    e (NormedSpace.exp z) = NormedSpace.exp (e z) := by
  have h := congrArg (· + (1 : A)) (map_exp_sub_one e z)
  simpa only [map_sub, map_one, sub_add_cancel] using h

private theorem exp_eq_under_algEquiv {x y : A}
    (hx : x ∈ eball 0 (NormedSpace.expSeries F A).radius)
    (hy : y ∈ eball 0 (NormedSpace.expSeries F A).radius) (e : A ≃ₐ[F] A)
    (heq : e (NormedSpace.exp x) = NormedSpace.exp y) : e x = y := by
  obtain ⟨c, hc, _, _, _, hcEval⟩ := exponentialChart (F := F) (A := A) univ isOpen_univ (mem_univ 0)
  have hmem : c.source ∈ 𝓝 (0 : A) := c.open_source.mem_nhds hc
  obtain ⟨p, hp, hpNorm⟩ := exists_pos_nat_norm_lt_one (F := F)
  have hT := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hpNorm
  have hsmall (z : A) : ∀ᶠ m : ℕ in atTop, ((p : F) ^ m) • z ∈ c.source :=
    (hT.zero_smul_const z).eventually_mem hmem
  obtain ⟨m, hm₁, hm₂⟩ := ((hsmall (e x)).and (hsmall y)).exists
  have hPower := congrArg (fun z : A => z ^ (p ^ m)) heq
  rw [← map_pow, ← exp_nat_smul_of_mem_eball hx, ← exp_nat_smul_of_mem_eball hy, map_exp] at hPower
  simp only [← Nat.cast_smul_eq_nsmul F, Nat.cast_pow, map_smul] at hPower
  have hscaled : ((p : F) ^ m) • e x = ((p : F) ^ m) • y :=
    c.injOn hm₁ hm₂ (by rw [hcEval, hcEval, hPower])
  exact (smul_right_injective A (pow_ne_zero m (Nat.cast_ne_zero.mpr hp))) hscaled

theorem exponentialConjugacy : ExponentialConjugacyStatement F A := by
  rintro _ ⟨e, x, hx, rfl⟩ _ ⟨f, y, hy, rfl⟩ h
  apply f.symm.injective
  rw [f.symm_apply_apply]
  apply exp_eq_under_algEquiv hx hy (e.trans f.symm)
  change f.symm (e (NormedSpace.exp x)) = NormedSpace.exp y
  apply f.injective
  simpa only [f.apply_symm_apply, map_exp] using h

end Langlands.HarmonicAnalysis.UnitConjugation
