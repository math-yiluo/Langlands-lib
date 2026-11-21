import Langlands.HarmonicAnalysis.Distribution.WeightedNormalCutoff
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform limits of polynomially bounded distribution evaluations on flat tests -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

universe u v w

variable {E : Type u} {N : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N]

/-- The complement of the zero section within an open product test domain. -/
def normalPuncturedDomain (Ω : Opens (E × N)) : Opens (E × N) :=
  ⟨(Ω : Set (E × N)) ∩ {x | x.2 ≠ 0}, Ω.isOpen.inter (isOpen_ne_fun continuous_snd continuous_const)⟩

private theorem outsideCutoff_zero_of_lt {K : Compacts (E × N)} (f : 𝓓_{K}(E × N, ℝ))
    {t : ℝ} (ht : 0 < t) (x : E × N) (hx : ‖x.2‖ < 1 / (2 * t)) :
    (f - normalCutoffTest t f) x = 0 := by
  let b : ContDiffBump (0 : N) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  change f x - b (t • x.2) * f x = 0
  have h : t • x.2 ∈ Metric.closedBall (0 : N) b.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le]
    change t * ‖x.2‖ ≤ 1 / 2
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * t)).mp hx
    nlinarith
  rw [b.one_of_mem_closedBall h, one_mul, sub_self]

/-- Remove the shrinking normal neighborhood and view the result as a test
on the punctured domain. -/
def puncturedCutoffTest {Ω : Opens (E × N)} {K : Compacts (E × N)} (hK : (K : Set (E × N)) ⊆ Ω)
    (f : 𝓓_{K}(E × N, ℝ)) (t : ℝ) (ht : 0 < t) : 𝓓(normalPuncturedDomain Ω, ℝ) := by
  let g := f - normalCutoffTest t f
  refine ⟨g, g.contDiff, g.hasCompactSupport, fun x hx => ⟨hK (g.tsupport_subset hx), ?_⟩⟩
  have hsupport : tsupport g ⊆ {y : E × N | 1 / (2 * t) ≤ ‖y.2‖} := by
    apply closure_minimal ?_ (isClosed_le continuous_const continuous_snd.norm)
    intro y hy
    exact le_of_not_gt fun hn => hy (outsideCutoff_zero_of_lt f ht y hn)
  intro hz
  have hp := hsupport hx
  change 1 / (2 * t) ≤ ‖x.2‖ at hp
  rw [hz, norm_zero] at hp
  exact (not_le_of_gt (by positivity : 0 < 1 / (2 * t))) hp

@[simp] theorem puncturedCutoffTest_apply {Ω : Opens (E × N)} {K : Compacts (E × N)}
    (hK : (K : Set (E × N)) ⊆ Ω) (f : 𝓓_{K}(E × N, ℝ)) (t : ℝ) (ht : 0 < t) (x : E × N) :
    puncturedCutoffTest hK f t ht x = f x - normalCutoffTest t f x := rfl

theorem tsupport_puncturedCutoffTest_subset {Ω : Opens (E × N)} {K : Compacts (E × N)}
    (hK : (K : Set (E × N)) ⊆ Ω) (f : 𝓓_{K}(E × N, ℝ)) (t : ℝ) (ht : 0 < t) :
    tsupport (puncturedCutoffTest hK f t ht) ⊆ K :=
  (f - normalCutoffTest t f).tsupport_subset

/-- A punctured distribution admits a bound by derivatives whose size is
measured in units of the indicated power of normal distance. -/
def HasWeightedNormalBound {Ω : Opens (E × N)} (T : 𝓓'(normalPuncturedDomain Ω, ℂ))
    (K : Compacts (E × N)) (d m : ℕ) (A : ℝ) : Prop :=
  ∀ f : 𝓓(normalPuncturedDomain Ω, ℝ), tsupport f ⊆ K → ∀ B : ℝ, 0 ≤ B →
    (∀ j ≤ d, ∀ x : E × N, ‖iteratedFDeriv ℝ j f x‖ ≤ B * ‖x.2‖ ^ m) → ‖T f‖ ≤ A * B

/-- A normal cutoff at integer scale `n+1`. -/
def puncturedCutoffSequence {Ω : Opens (E × N)} {K : Compacts (E × N)} (hK : (K : Set (E × N)) ⊆ Ω)
    (f : 𝓓_{K}(E × N, ℝ)) (n : ℕ) : 𝓓(normalPuncturedDomain Ω, ℝ) :=
  puncturedCutoffTest hK f ((n : ℝ) + 1) (by positivity)

/-- If the fixed support already avoids the section, the cutoff sequence
eventually gives the original test on the punctured domain. -/
theorem puncturedCutoffSequence_eventuallyEq {Ω : Opens (E × N)} {K : Compacts (E × N)}
    (hK : (K : Set (E × N)) ⊆ Ω) (hOff : (K : Set (E × N)) ⊆ normalPuncturedDomain Ω)
    (f : 𝓓_{K}(E × N, ℝ)) :
    puncturedCutoffSequence hK f =ᶠ[atTop] fun _ => TestFunction.ofSupportedIn hOff f := by
  let b : ContDiffBump (0 : N) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  obtain ⟨δ, hδ, hMin⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ (K : Set (E × N)), δ ≤ ‖x.2‖ := by
    by_cases hn : (K : Set (E × N)).Nonempty
    · obtain ⟨x, hx, hmin⟩ := K.isCompact.exists_isMinOn hn continuous_snd.norm.continuousOn
      exact ⟨‖x.2‖, norm_pos_iff.mpr (hOff hx).2, fun y hy => hmin hy⟩
    · exact ⟨1, one_pos, fun x hx => (hn ⟨x, hx⟩).elim⟩
  have hs : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [hs.eventually_ge_atTop δ⁻¹] with n hn
  ext x
  rw [puncturedCutoffSequence, puncturedCutoffTest_apply]
  change f x - b (((n : ℝ) + 1) • x.2) * f x = f x
  by_cases hx : x ∈ (K : Set (E × N))
  · have h : 1 ≤ ‖((n : ℝ) + 1) • x.2‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
      calc
        1 = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
        _ ≤ ((n : ℝ) + 1) * ‖x.2‖ :=
          mul_le_mul hn (hMin x hx) hδ.le (by positivity)
    rw [b.zero_of_le_dist (by simpa only [dist_zero_right] using h), zero_mul, sub_zero]
  · have hz : f x = 0 := f.zero_on_compl hx
    rw [hz, mul_zero, sub_zero]

/-- Polynomially bounded evaluations of the normal cutoffs of a flat test converge uniformly
in every parameter set with a common bound. -/
theorem exists_uniformCutoffLimit {Ω : Opens (E × N)} {K : Compacts (E × N)}
    (hK : (K : Set (E × N)) ⊆ Ω) {P : Type w} (S : Set P)
    (T : P → 𝓓'(normalPuncturedDomain Ω, ℂ)) {d m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hT : ∀ z ∈ S, HasWeightedNormalBound (T z) K d m A) (f : 𝓓_{K}(E × N, ℝ))
    (hf : ∀ x : E, ∀ i ≤ d + m, iteratedFDeriv ℝ i f (x, 0) = 0) :
    ∃ F : P → ℂ, TendstoUniformlyOn (fun n z => T z (puncturedCutoffSequence hK f n)) F atTop S := by
  classical
  let φ := puncturedCutoffSequence hK f
  let s (n : ℕ) : ℝ := (n : ℝ) + 1
  let q := ContDiffMapSupportedIn.supSeminorm ℝ (E × N) ℝ ⊤ K (d + m + 1) f
  have hq : 0 ≤ q := apply_nonneg _ _
  obtain ⟨C, hC, hCut⟩ := exists_weighted_normalCutoff_bound (E := E) (N := N) d m
  have hCut' (n j : ℕ) (hj : j ≤ d) (x : E × N) :
      ‖iteratedFDeriv ℝ j (normalCutoffTest (s n) f) x‖ ≤ (C * q) * ‖x.2‖ ^ m * (s n)⁻¹ :=
    hCut f hf (s n) (le_add_of_nonneg_left (Nat.cast_nonneg n)) j hj x
  have hDiff (n k : ℕ) (z : P) (hz : z ∈ S) :
      dist (T z (φ n)) (T z (φ k)) ≤ A * ((C * q) * ((s n)⁻¹ + (s k)⁻¹)) := by
    let g := φ n - φ k
    have hG : (g : E × N → ℝ) =
        (normalCutoffTest (s k) f : E × N → ℝ) - (normalCutoffTest (s n) f : E × N → ℝ) := by
      funext x
      simp only [g, φ, puncturedCutoffSequence, puncturedCutoffTest_apply, s, sub_apply, Pi.sub_apply]
      ring
    have hGK : tsupport g ⊆ K := (tsupport_sub _ _).trans (union_subset
      (tsupport_puncturedCutoffTest_subset hK f _ _) (tsupport_puncturedCutoffTest_subset hK f _ _))
    rw [dist_eq_norm, ← map_sub]
    apply hT z hz g hGK _ (by positivity)
    intro j hj x
    rw [hG, iteratedFDeriv_sub_apply ((normalCutoffTest (s k) f).contDiff.contDiffAt.of_le (by simp))
      ((normalCutoffTest (s n) f).contDiff.contDiffAt.of_le (by simp))]
    calc
      _ ≤ ‖iteratedFDeriv ℝ j (normalCutoffTest (s k) f) x‖ +
          ‖iteratedFDeriv ℝ j (normalCutoffTest (s n) f) x‖ := norm_sub_le _ _
      _ ≤ (C * q) * ‖x.2‖ ^ m * (s k)⁻¹ + (C * q) * ‖x.2‖ ^ m * (s n)⁻¹ :=
        add_le_add (hCut' k j hj x) (hCut' n j hj x)
      _ = _ := by ring
  have hs : Tendsto (fun n : ℕ => (s n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hSmall : Tendsto (fun n : ℕ => A * (C * q) * (2 * (s n)⁻¹)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hs.const_mul 2).const_mul (A * (C * q))
  have hUnif : UniformCauchySeqOn (fun n z => T z (φ n)) atTop S := by
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hSmall.eventually (gt_mem_nhds hε))
    refine ⟨M, fun n hn k hk z hz => (hDiff n k z hz).trans_lt ?_⟩
    have hle (l : ℕ) (hl : M ≤ l) : (s l)⁻¹ ≤ (s M)⁻¹ := by
      have hb : s M ≤ s l := add_le_add (Nat.cast_le.mpr hl) le_rfl
      exact inv_anti₀ (by dsimp only [s]; positivity) hb
    apply lt_of_le_of_lt _ (hM M le_rfl)
    simpa only [mul_assoc, two_mul] using
      mul_le_mul_of_nonneg_left (add_le_add (hle n hn) (hle k hk)) (mul_nonneg hA (mul_nonneg hC hq))
  have hLimit (z : P) (hz : z ∈ S) : ∃ c, Tendsto (fun n => T z (φ n)) atTop (𝓝 c) := by
    apply cauchySeq_tendsto_of_complete
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨M, hM⟩ := Metric.uniformCauchySeqOn_iff.1 hUnif ε hε
    exact ⟨M, fun n hn k hk => hM n hn k hk z hz⟩
  let F (z : P) := if hz : z ∈ S then (hLimit z hz).choose else 0
  refine ⟨F, hUnif.tendstoUniformlyOn_of_tendsto fun z hz => ?_⟩
  rw [show F z = (hLimit z hz).choose from dite_eq_left hz]
  exact (hLimit z hz).choose_spec

/-- On a complex parameter domain with a common bound, the cutoff limit
is holomorphic if each punctured evaluation is holomorphic. -/
theorem exists_holomorphicCutoffLimit {Ω : Opens (E × N)} {K : Compacts (E × N)}
    (hK : (K : Set (E × N)) ⊆ Ω) {S : Set ℂ} (hS : IsOpen S)
    (T : ℂ → 𝓓'(normalPuncturedDomain Ω, ℂ)) {d m : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hT : ∀ z ∈ S, HasWeightedNormalBound (T z) K d m A)
    (hHol : ∀ g : 𝓓(normalPuncturedDomain Ω, ℝ), DifferentiableOn ℂ (fun z => T z g) S)
    (f : 𝓓_{K}(E × N, ℝ)) (hf : ∀ x : E, ∀ i ≤ d + m, iteratedFDeriv ℝ i f (x, 0) = 0) :
    ∃ F : ℂ → ℂ, TendstoUniformlyOn (fun n z => T z (puncturedCutoffSequence hK f n)) F atTop S ∧
      DifferentiableOn ℂ F S := by
  obtain ⟨F, hF⟩ := exists_uniformCutoffLimit hK S T hA hT f hf
  exact ⟨F, hF, hF.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun n => hHol (puncturedCutoffSequence hK f n)) hS⟩

/-- Flat tests have a uniform cutoff limit under a common weighted distribution estimate. -/
def FlatNormalCutoffLimitStatement : Prop :=
  ∀ (E : Type u) (N : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (Ω : Opens (E × N)) (K : Compacts (E × N)) (hK : (K : Set (E × N)) ⊆ Ω)
    (P : Type w) (S : Set P) (T : P → 𝓓'(normalPuncturedDomain Ω, ℂ)) (d m : ℕ) (A : ℝ),
    0 ≤ A → (∀ z ∈ S, HasWeightedNormalBound (T z) K d m A) →
    ∀ f : 𝓓_{K}(E × N, ℝ), (∀ x : E, ∀ i ≤ d + m, iteratedFDeriv ℝ i f (x, 0) = 0) →
      ∃ F : P → ℂ, TendstoUniformlyOn (fun n z => T z (puncturedCutoffSequence hK f n)) F atTop S

theorem flatNormalCutoffLimit : FlatNormalCutoffLimitStatement.{u, v, w} := by
  intro E N _ _ _ _ _ Ω K hK P S T d m A hA hT f hf
  exact exists_uniformCutoffLimit hK S T hA hT f hf

end Langlands.HarmonicAnalysis
