import Langlands.HarmonicAnalysis.Distribution.VectorFieldLeadingJet
import Langlands.HarmonicAnalysis.Distribution.ProductJetCovariance
import Langlands.HarmonicAnalysis.Distribution.SmoothVectorFieldTest

/-! # Vanishing of eigen-distributions on a zero section -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {Ω Ω₀ : Opens X} {W : X → X} {b : X → ℝ}

/-- The derivative along a vector field with an order-zero correction. -/
def shiftedVectorFieldDerivativeTest (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (f : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  smoothVectorFieldDerivativeTest hW f + localScalarMultiplierCLM hb f

theorem monoCLM_shiftedVectorFieldDerivativeTest (hΩ : Ω₀ ≤ Ω)
    (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω) (f : 𝓓(Ω₀, ℝ)) :
    (TestFunction.monoCLM ℝ (shiftedVectorFieldDerivativeTest (hW.mono hΩ) (hb.mono hΩ) f) :
      𝓓(Ω, ℝ)) = shiftedVectorFieldDerivativeTest hW hb (TestFunction.monoCLM ℝ f) := by
  have hcoe (g : 𝓓(Ω₀, ℝ)) :
      ((TestFunction.monoCLM ℝ g : 𝓓(Ω, ℝ)) : X → ℝ) = g := by simp [hΩ]
  ext x
  rw [congrFun (hcoe _)]
  simp only [shiftedVectorFieldDerivativeTest, add_apply, smoothVectorFieldDerivativeTest_apply,
    localScalarMultiplierCLM_apply, hcoe]

private theorem iteratedFDeriv_shiftedVectorFieldDerivativeTest
    (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω) (f : 𝓓(Ω, ℝ))
    {x : X} (hx : x ∈ Ω) (hW₀ : W x = 0) (hb₀ : b x = 0) (k : ℕ)
    (hflat : ∀ j < k, iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (shiftedVectorFieldDerivativeTest hW hb f) x =
      jetSlotSum k (fderiv ℝ W x) (iteratedFDeriv ℝ k f x) := by
  let g := smoothVectorFieldDerivativeTest hW f
  let h := localScalarMultiplierCLM hb f
  have hg : ContDiffAt ℝ k g x := g.contDiff.contDiffAt.of_le (by simp)
  have hh : ContDiffAt ℝ k h x := h.contDiff.contDiffAt.of_le (by simp)
  change iteratedFDeriv ℝ k ((g : X → ℝ) + (h : X → ℝ)) x = _
  rw [iteratedFDeriv_add_apply hg hh]
  change iteratedFDeriv ℝ k (fun y => fderiv ℝ f y (W y)) x +
    iteratedFDeriv ℝ k (fun y => f y * b y) x = _
  rw [iteratedFDeriv_vectorField_of_eq_zero Ω.isOpen f.contDiff hW hx hW₀ k hflat,
    iteratedFDeriv_mul_eq_zero_of_lower_eq_zero Ω.isOpen f.contDiff hb hx hb₀ k hflat, add_zero]

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  {U : Opens E} {V : Opens N}

local notation "Δ" => productTestDomain U V

private theorem eval_eq_zero_of_lower_jets {A : E × N → E × N} {c : E × N → ℝ}
    (hA : ContDiffOn ℝ ∞ A Δ) (hc : ContDiffOn ℝ ∞ c Δ)
    (hV₀ : (0 : N) ∈ V) (hzero : ∀ x ∈ U, A (x, 0) = 0 ∧ c (x, 0) = 0)
    (hnil : ∀ x ∈ U, IsNilpotent (fderiv ℝ A (x, 0)).toLinearMap)
    (T : 𝓓'(Δ, ℂ)) (eigen : ℂ) (heigen : eigen ≠ 0)
    (hT : ∀ g : 𝓓(Δ, ℝ), T (shiftedVectorFieldDerivativeTest hA hc g) = eigen * T g)
    (k : ℕ) (hord : HasTransverseJetOrder T k) (f : 𝓓(Δ, ℝ))
    (hflat : ∀ j < k, transverseProductJetCLM j f = 0) : T f = 0 := by
  let D := shiftedVectorFieldDerivativeTest hA hc
  let m := k * Module.finrank ℝ (E × N) + 1
  have hfull (j : ℕ) (hj : j < k) (x : E) : iteratedFDeriv ℝ j f (x, 0) = 0 := by
    apply iteratedFDeriv_eq_zero_of_transverseJets f.contDiff j _ j le_rfl x
    intro y l hl v
    rw [← transverseProductJetCLM_apply, hflat l (hl.trans_lt hj)]
    rfl
  have hjet (x : E) (hx : x ∈ U) (p : ℕ) (j : ℕ) (hj : j ≤ k) :
      iteratedFDeriv ℝ j (D^[p] f) (x, 0) =
        (jetSlotSum j (fderiv ℝ A (x, 0)) ^ p) (iteratedFDeriv ℝ j f (x, 0)) := by
    induction p generalizing j with
    | zero => simp
    | succ p ih =>
      rw [Function.iterate_succ_apply']
      have hx' : (x, 0) ∈ Δ := ⟨hx, hV₀⟩
      have hflat' (l : ℕ) (hl : l < j) : iteratedFDeriv ℝ l (D^[p] f) (x, 0) = 0 := by
        rw [ih l (hl.le.trans hj), hfull l (hl.trans_le hj) x, map_zero]
      rw [iteratedFDeriv_shiftedVectorFieldDerivativeTest hA hc _ hx'
        (hzero x hx).1 (hzero x hx).2 j hflat', ih j hj, pow_succ', Module.End.mul_apply]
  have hjet₀ (j : ℕ) (hj : j ≤ k) : transverseProductJetCLM j (D^[m] f) = 0 := by
    ext1 x
    ext1 v
    rw [transverseProductJetCLM_apply]
    change iteratedFDeriv ℝ j (D^[m] f) (x, 0) (fun l => (0, v l)) = 0
    by_cases hx : x ∈ U
    · rw [hjet x hx m j hj]
      rcases hj.lt_or_eq with hjk | rfl
      · rw [hfull j hjk x, map_zero, zero_apply]
      · rw [show (jetSlotSum (F := ℝ) j (fderiv ℝ A (x, 0))) ^ m = 0 from
          jetSlotSum_finrank_pow_eq_zero j _ (hnil x hx), LinearMap.zero_apply, zero_apply]
    · have hx' : (x, 0) ∉ tsupport (iteratedFDeriv ℝ j (D^[m] f : E × N → ℝ)) :=
        fun h => hx ((D^[m] f).tsupport_subset (tsupport_iteratedFDeriv_subset j h)).1
      rw [image_eq_zero_of_notMem_tsupport hx', zero_apply]
  have hpow (p : ℕ) : T (D^[p] f) = eigen ^ p * T f := by
    induction p with
    | zero => simp
    | succ p ih => rw [Function.iterate_succ_apply', hT, ih, pow_succ', mul_assoc]
  exact (mul_eq_zero.mp ((hpow m).symm.trans (hord _ hjet₀))).resolve_left (pow_ne_zero _ heigen)

private theorem eq_zero_of_hasTransverseJetOrder {A : E × N → E × N} {c : E × N → ℝ}
    (hA : ContDiffOn ℝ ∞ A Δ) (hc : ContDiffOn ℝ ∞ c Δ) (hV₀ : (0 : N) ∈ V)
    (hzero : ∀ x ∈ U, A (x, 0) = 0 ∧ c (x, 0) = 0)
    (hnil : ∀ x ∈ U, IsNilpotent (fderiv ℝ A (x, 0)).toLinearMap)
    (T : 𝓓'(Δ, ℂ)) (eigen : ℂ) (heigen : eigen ≠ 0)
    (hT : ∀ g : 𝓓(Δ, ℝ), T (shiftedVectorFieldDerivativeTest hA hc g) = eigen * T g)
    (k : ℕ) (hord : HasTransverseJetOrder T k) : T = 0 := by
  have heval := eval_eq_zero_of_lower_jets hA hc hV₀ hzero hnil T eigen heigen hT
  induction k with
  | zero =>
    apply DFunLike.ext
    intro f
    exact heval 0 hord f (fun j hj => (Nat.not_lt_zero j hj).elim)
  | succ k ih =>
    apply ih
    intro f hf
    exact heval (k + 1) hord f (fun j hj => hf j (Nat.le_of_lt_succ hj))

/-- A distribution supported on the zero section with a nonzero eigenvalue
for a vanishing field and correction is zero if the field is linearized
nilpotently along that section. -/
theorem distribution_eq_zero_of_zeroSection_field {A : E × N → E × N} {c : E × N → ℝ}
    (hA : ContDiffOn ℝ ∞ A Δ) (hc : ContDiffOn ℝ ∞ c Δ) (hV₀ : (0 : N) ∈ V)
    (hzero : ∀ x ∈ U, A (x, 0) = 0 ∧ c (x, 0) = 0)
    (hnil : ∀ x ∈ U, IsNilpotent (fderiv ℝ A (x, 0)).toLinearMap)
    (T : 𝓓'(Δ, ℂ)) (hs : Distribution.IsVanishingOn T {z : E × N | z.2 ≠ 0})
    (eigen : ℂ) (heigen : eigen ≠ 0)
    (hT : ∀ g : 𝓓(Δ, ℝ), T (shiftedVectorFieldDerivativeTest hA hc g) = eigen * T g) : T = 0 := by
  let Good := {s : Opens (E × N) // Distribution.IsVanishingOn T (s : Set (E × N))}
  let s (j : Good) : Set (E × N) := j.val
  have hcover : (Δ : Set (E × N)) ⊆ ⋃ j, s j := by
    rintro ⟨x, y⟩ hxy
    have hx : x ∈ U := hxy.1
    by_cases hy : y = 0
    · subst y
      obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (U.isOpen.mem_nhds hx)
      obtain ⟨q, hq, hqV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (V.isOpen.mem_nhds hV₀)
      let U₀ : Opens E := ⟨Metric.ball x r, Metric.isOpen_ball⟩
      let V₀ : Opens N := ⟨Metric.ball 0 q, Metric.isOpen_ball⟩
      let K : Compacts (E × N) := ⟨Metric.closedBall x r ×ˢ Metric.closedBall 0 q,
        (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)⟩
      have hK : (K : Set (E × N)) ⊆ Δ := Set.prod_mono hrU hqV
      have hK₀ : (productTestDomain U₀ V₀ : Set (E × N)) ⊆ K :=
        Set.prod_mono Metric.ball_subset_closedBall Metric.ball_subset_closedBall
      have hm : productTestDomain U₀ V₀ ≤ Δ := hK₀.trans hK
      let i : 𝓓(productTestDomain U₀ V₀, ℝ) →L[ℝ] 𝓓(Δ, ℝ) := TestFunction.monoCLM ℝ
      let T₀ := T.comp i
      have hord : HasTransverseJetOrder T₀ (smoothDistributionCompactOrder T hK) :=
        hasTransverseJetOrder_comp_monoCLM T hs hK hK₀
      have hcov (g : 𝓓(productTestDomain U₀ V₀, ℝ)) :
          T₀ (shiftedVectorFieldDerivativeTest (hA.mono hm) (hc.mono hm) g) = eigen * T₀ g := by
        change T (TestFunction.monoCLM ℝ
          (shiftedVectorFieldDerivativeTest (hA.mono hm) (hc.mono hm) g)) = eigen * T (i g)
        rw [monoCLM_shiftedVectorFieldDerivativeTest hm]
        exact hT _
      have hzero₀ : T₀ = 0 := eq_zero_of_hasTransverseJetOrder (hA.mono hm) (hc.mono hm)
        (Metric.mem_ball_self hq)
        (fun z hz => hzero z (hrU (Metric.ball_subset_closedBall hz)))
        (fun z hz => hnil z (hrU (Metric.ball_subset_closedBall hz))) T₀ eigen heigen hcov _ hord
      have hv : Distribution.IsVanishingOn T (productTestDomain U₀ V₀ : Set (E × N)) := by
        intro f hf
        let g : 𝓓(productTestDomain U₀ V₀, ℝ) := ⟨f, f.contDiff, f.hasCompactSupport, hf⟩
        have hgf : i g = f := by
          have hcoe : (i g : E × N → ℝ) = g := by simp [i, hm]
          ext z
          exact congrFun hcoe z
        rw [← hgf]
        change T₀ g = 0
        rw [hzero₀]
        rfl
      exact mem_iUnion.mpr ⟨⟨productTestDomain U₀ V₀, hv⟩,
        Metric.mem_ball_self hr, Metric.mem_ball_self hq⟩
    · let O : Opens (E × N) := ⟨{z | z.2 ≠ 0}, isOpen_ne_fun continuous_snd continuous_const⟩
      exact mem_iUnion.mpr ⟨⟨O, hs⟩, hy⟩
  have hv := smoothDistribution_isVanishingOn_iUnion T s (fun j => j.val.isOpen) (fun j => j.property)
  apply DFunLike.ext
  intro f
  exact hv f (f.tsupport_subset.trans hcover)

universe u v

/-- Nonzero infinitesimal covariance eliminates support on the zero section
when the field and scalar term vanish there and the field derivative is nilpotent. -/
def ZeroSectionFieldVanishingStatement : Prop :=
  ∀ (E : Type u) (N : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] (U : Opens E) (V : Opens N),
    (0 : N) ∈ V →
    ∀ (A : E × N → E × N) (c : E × N → ℝ)
      (hA : ContDiffOn ℝ ∞ A (productTestDomain U V))
      (hc : ContDiffOn ℝ ∞ c (productTestDomain U V)),
      (∀ x ∈ U, A (x, 0) = 0 ∧ c (x, 0) = 0) →
      (∀ x ∈ U, IsNilpotent (fderiv ℝ A (x, 0)).toLinearMap) →
      ∀ T : 𝓓'(productTestDomain U V, ℂ),
        Distribution.IsVanishingOn T {z : E × N | z.2 ≠ 0} →
        ∀ eigen : ℂ, eigen ≠ 0 →
          (∀ g : 𝓓(productTestDomain U V, ℝ),
            T (shiftedVectorFieldDerivativeTest hA hc g) = eigen * T g) → T = 0

theorem zeroSectionFieldVanishing : ZeroSectionFieldVanishingStatement.{u, v} := by
  intro E N _ _ _ _ _ _ U V hV A c hA hc hzero hnil T hs eigen heigen hT
  exact distribution_eq_zero_of_zeroSection_field hA hc hV hzero hnil T hs eigen heigen hT

end Langlands.HarmonicAnalysis
