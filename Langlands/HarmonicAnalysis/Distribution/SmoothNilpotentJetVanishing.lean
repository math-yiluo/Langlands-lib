import Langlands.HarmonicAnalysis.Distribution.SmoothVectorFieldJet

/-! # Vanishing from nilpotence on full jets along a product zero section -/

noncomputable section

open Filter Set TopologicalSpace
open scoped Classical ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

open Langlands.Analysis (fderiv_fst_slice_apply)

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem iteratedFDeriv_mul_of_lower_zero {f a : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (ha : ContDiff ℝ ∞ a) {x : E} (k : ℕ) (hLower : ∀ j < k, iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (fun y => a y * f y) x = a x • iteratedFDeriv ℝ k f x := by
  let b (y : E) := a y - a x
  have hb : ContDiff ℝ ∞ b := ha.sub contDiff_const
  have hB0 : iteratedFDeriv ℝ 0 b x = 0 := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [iteratedFDeriv_zero_apply, b, sub_self, zero_apply]
  have hB : iteratedFDeriv ℝ k (fun y => b y * f y) x = 0 := by
    have hd := norm_iteratedFDeriv_mul_le hb hf x (n := k) (by simp)
    apply norm_eq_zero.mp
    refine le_antisymm (hd.trans_eq ?_) (norm_nonneg _)
    apply Finset.sum_eq_zero
    intro i hiMem
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hiMem)
    by_cases hi : i = 0
    · subst i
      rw [hB0, norm_zero, mul_zero, zero_mul]
    · rw [hLower (k - i) (by omega), norm_zero, mul_zero]
  have hEq : (fun y => b y * f y) = (fun y => a y * f y) - (fun y => a x • f y) := by
    funext y
    exact sub_mul _ _ _
  rw [hEq, iteratedFDeriv_sub_apply ((ha.mul hf).contDiffAt.of_le (by simp))
    ((hf.const_smul (a x)).contDiffAt.of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by simp))] at hB
  exact sub_eq_zero.mp hB

/-- If a field vanishes along a zero section, nilpotence on its normal derivative lifts
with one extra power to the full derivative. -/
theorem fullFieldDerivative_pow_succ_zero {V : E × W → E × W} (hV : ContDiff ℝ ∞ V)
    (hV0 : ∀ x, V (x, 0) = 0) {m : ℕ} (x : E) (hNil : productNormalDerivative V x ^ m = 0) :
    fderiv ℝ V (x, 0) ^ (m + 1) = 0 := by
  let A := fderiv ℝ V (x, 0)
  let N := productNormalDerivative V x
  have hTang (v : E) : A (v, 0) = 0 := by
    change fderiv ℝ V (x, 0) (v, 0) = 0
    rw [← fderiv_fst_slice_apply (hV.differentiable (by simp) (x, 0)),
      show (fun x : E => V (x, 0)) = 0 from funext hV0, fderiv_zero]
    simp
  have hComm (v : E × W) : (A v).2 = N v.2 := by
    nth_rw 1 [show v = (v.1, 0) + (0, v.2) by simp]
    rw [map_add, Prod.snd_add, hTang, Prod.snd_zero, zero_add]
    rfl
  have hPow (p : ℕ) (v : E × W) : ((A ^ p) v).2 = (N ^ p) v.2 := by
    induction p with
    | zero => rfl
    | succ p ih =>
      rw [pow_succ' A, pow_succ' N]
      change (A ((A ^ p) v)).2 = N ((N ^ p) v.2)
      rw [hComm, ih]
  apply ContinuousLinearMap.ext
  intro v
  change (A ^ (m + 1)) v = 0
  rw [pow_succ']
  change A ((A ^ m) v) = 0
  have hSecond : ((A ^ m) v).2 = 0 := by rw [hPow, show N ^ m = 0 from hNil, zero_apply]
  rw [show (A ^ m) v = (((A ^ m) v).1, 0) from Prod.ext rfl hSecond]
  exact hTang _

section TestOperator

variable {Ω : Opens E}

/-- A first-order operator on smooth complex tests, with an extra smooth multiplier
on the derivative term. -/
def smoothFirstOrderTest (a b : E → ℂ) (V : E → E) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hV : ContDiff ℝ ∞ V) (f : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) := by
  let g (y : E) := a y * fderiv ℝ f y (V y) + b y * f y
  have hZero (y : E) (hy : y ∉ tsupport f) : g y = 0 := by
    dsimp only [g]
    rw [fderiv_of_notMem_tsupport ℝ hy, zero_apply, image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero, add_zero]
  have hg : Function.support g ⊆ tsupport f := fun y hy => by_contra fun h => hy (hZero y h)
  exact ⟨g, (ha.mul ((f.contDiff.fderiv_right (by simp)).clm_apply hV)).add (hb.mul f.contDiff),
    HasCompactSupport.of_support_subset_isCompact f.hasCompactSupport hg,
    (closure_minimal hg (isClosed_tsupport f)).trans f.tsupport_subset⟩

@[simp] theorem smoothFirstOrderTest_apply (a b : E → ℂ) (V : E → E) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hV : ContDiff ℝ ∞ V) (f : 𝓓(Ω, ℂ)) (y : E) :
    smoothFirstOrderTest a b V ha hb hV f y = a y * fderiv ℝ f y (V y) + b y * f y := rfl

theorem tsupport_smoothFirstOrderTest_subset (a b : E → ℂ) (V : E → E) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hV : ContDiff ℝ ∞ V) (f : 𝓓(Ω, ℂ)) :
    tsupport (smoothFirstOrderTest a b V ha hb hV f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro y hy
  by_contra h
  exact hy (by simp [fderiv_of_notMem_tsupport ℝ h, image_eq_zero_of_notMem_tsupport h])

variable [FiniteDimensional ℝ E]

private theorem iteratedFDeriv_smoothFirstOrderTest (a b : E → ℂ) (V : E → E)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hV : ContDiff ℝ ∞ V) (f : 𝓓(Ω, ℂ))
    (x : E) (hVx : V x = 0) (hbx : b x = 0) (k : ℕ)
    (hLower : ∀ j < k, iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (smoothFirstOrderTest a b V ha hb hV f) x =
      (a x • jetSlotAction (fderiv ℝ V x) k) (iteratedFDeriv ℝ k f x) := by
  let g := fun y => fderiv ℝ f y (V y)
  have hg : ContDiff ℝ ∞ g := (f.contDiff.fderiv_right (by simp)).clm_apply hV
  have hG (j : ℕ) (hj : j < k) : iteratedFDeriv ℝ j g x = 0 := by
    rw [smoothVectorFieldJet (⇑f) V x j f.contDiff hV hVx (fun i hi => hLower i (hi.trans hj)),
      hLower j hj, map_zero]
  change iteratedFDeriv ℝ k ((fun y => a y * g y) + (fun y => b y * f y)) x = _
  rw [iteratedFDeriv_add_apply ((ha.mul hg).contDiffAt.of_le (by simp))
      ((hb.mul f.contDiff).contDiffAt.of_le (by simp)),
    iteratedFDeriv_mul_of_lower_zero hg ha k hG,
    iteratedFDeriv_mul_of_lower_zero f.contDiff hb k hLower, hbx, zero_smul, add_zero,
    smoothVectorFieldJet (⇑f) V x k f.contDiff hV hVx hLower]
  rfl

end TestOperator

private def realInputDistribution {Ω : Opens (E × W)} (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) : 𝓓'(Ω, ℂ) :=
  (T.restrictScalars ℝ).comp (TestFunction.postcompCLM Complex.ofRealCLM)

private theorem complexDistribution_zero_of_flatProductJet [FiniteDimensional ℝ W]
    {Ω : Opens (E × W)} (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ)
    (hT : Distribution.IsVanishingOn (⇑T) {z : E × W | z.2 ≠ 0})
    {K : Compacts (E × W)} (hK : (K : Set (E × W)) ⊆ Ω) (f : 𝓓_{K}(E × W, ℂ))
    (hflat : ∀ x : E, ∀ i ≤ smoothDistributionCompactOrder (realInputDistribution T) hK,
      iteratedFDeriv ℝ i f (x, 0) = 0) : T (TestFunction.ofSupportedIn hK f) = 0 := by
  let D := realInputDistribution T
  let ofReal : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℂ) := TestFunction.postcompCLM Complex.ofRealCLM
  have hD : Distribution.IsVanishingOn D {z : E × W | z.2 ≠ 0} := by
    intro u hu
    change T (ofReal u) = 0
    apply hT
    exact (tsupport_comp_subset (map_zero Complex.ofRealCLM) (⇑u)).trans hu
  let fRe := ContDiffMapSupportedIn.postcompCLM Complex.reCLM f
  let fIm := ContDiffMapSupportedIn.postcompCLM Complex.imCLM f
  have hReal (L : ℂ →L[ℝ] ℝ) : D (TestFunction.ofSupportedIn hK
      (ContDiffMapSupportedIn.postcompCLM L f)) = 0 := by
    apply distribution_eq_zero_of_flatProductJet D hD hK
    intro x i hi
    change iteratedFDeriv ℝ i (L ∘ (⇑f)) (x, 0) = 0
    rw [L.iteratedFDeriv_comp_left f.contDiff.contDiffAt (by simp), hflat x i hi]
    ext v
    simp
  have hSplit : TestFunction.ofSupportedIn hK f =
      ofReal (TestFunction.ofSupportedIn hK fRe) + Complex.I • ofReal (TestFunction.ofSupportedIn hK fIm) := by
    ext y
    change f y = ((f y).re : ℂ) + Complex.I * ((f y).im : ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (f y)).symm
  rw [hSplit, map_add, map_smul]
  change D (TestFunction.ofSupportedIn hK fRe) + Complex.I • D (TestFunction.ofSupportedIn hK fIm) = 0
  rw [hReal Complex.reCLM, hReal Complex.imCLM, smul_zero, add_zero]

/-- A distribution supported on a product zero section is zero if it annihilates
the identity plus a first-order operator with uniformly nilpotent jet action. -/
def SmoothNilpotentJetVanishingStatement : Prop :=
  ∀ {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Ω : Opens (E × W)} (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ),
    Distribution.IsVanishingOn (⇑T) {z : E × W | z.2 ≠ 0} →
    ∀ (a b : E × W → ℂ) (V : E × W → E × W) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
      (hV : ContDiff ℝ ∞ V) (m : ℕ),
      (∀ x : E, V (x, 0) = 0) → (∀ x : E, b (x, 0) = 0) →
      (∀ x : E, productNormalDerivative V x ^ m = 0) →
      (∀ f : 𝓓(Ω, ℂ), T (f + smoothFirstOrderTest a b V ha hb hV f) = 0) → T = 0

set_option maxHeartbeats 850000 in
theorem smoothNilpotentJetVanishing : SmoothNilpotentJetVanishingStatement := by
  intro E W _ _ _ _ _ _ Ω T hT a b V ha hb hV m hV0 hb0 hN hId
  let D := smoothFirstOrderTest (Ω := Ω) a b V ha hb hV
  have hSupport (f : 𝓓(Ω, ℂ)) (p : ℕ) : tsupport (D^[p] f) ⊆ tsupport f := by
    induction p with
    | zero => exact Subset.rfl
    | succ p ih =>
      rw [Function.iterate_succ_apply']
      exact (tsupport_smoothFirstOrderTest_subset a b V ha hb hV _).trans ih
  have hIterate : ∀ k : ℕ, ∃ q : ℕ, ∀ (f : 𝓓(Ω, ℂ)) (x : E) (j : ℕ), j < k →
      iteratedFDeriv ℝ j (D^[q] f) (x, 0) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨0, fun _ _ _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      obtain ⟨q, hq⟩ := ih
      let J (x : E) := a (x, 0) • jetSlotAction (fderiv ℝ V (x, 0)) k
      have hJ (x : E) : J x ^ (k * (m + 1) + 1) = 0 :=
        smoothJetSlotNilpotence k (m + 1) _ _ (fullFieldDerivative_pow_succ_zero hV hV0 x (hN x))
      have hP (f : 𝓓(Ω, ℂ)) (x : E) (p : ℕ) :
          (∀ j < k, iteratedFDeriv ℝ j (D^[p] (D^[q] f)) (x, 0) = 0) ∧
          iteratedFDeriv ℝ k (D^[p] (D^[q] f)) (x, 0) =
            (J x ^ p) (iteratedFDeriv ℝ k (D^[q] f) (x, 0)) := by
        induction p with
        | zero => exact ⟨fun j hj => hq f x j hj, rfl⟩
        | succ p hp =>
          constructor
          · intro j hj
            rw [Function.iterate_succ_apply', iteratedFDeriv_smoothFirstOrderTest
              a b V ha hb hV _ _ (hV0 x) (hb0 x) j (fun i hi => hp.1 i (hi.trans hj)), hp.1 j hj, map_zero]
          · rw [Function.iterate_succ_apply', iteratedFDeriv_smoothFirstOrderTest
              a b V ha hb hV _ _ (hV0 x) (hb0 x) k hp.1, hp.2, pow_succ']
            rfl
      let p := k * (m + 1) + 1
      refine ⟨p + q, fun f x j hj => ?_⟩
      have hp := hP f x p
      rw [Function.iterate_add_apply]
      rcases Nat.lt_succ_iff.mp hj |>.lt_or_eq with hj' | rfl
      · exact hp.1 j hj'
      · rw [hp.2, hJ x]
        rfl
  apply ContinuousLinearMap.ext
  intro f
  let K : Compacts (E × W) := ⟨tsupport f, f.hasCompactSupport⟩
  have hK : (K : Set (E × W)) ⊆ Ω := f.tsupport_subset
  obtain ⟨q, hq⟩ := hIterate (smoothDistributionCompactOrder (realInputDistribution T) hK + 1)
  let g : 𝓓_{K}(E × W, ℂ) := ContDiffMapSupportedIn.of_support_subset (D^[q] f).contDiff
    ((subset_tsupport _).trans (hSupport f q))
  have hg : T (D^[q] f) = 0 := complexDistribution_zero_of_flatProductJet T hT hK g
    (fun x i hi => hq f x i (Nat.lt_succ_of_le hi))
  have hVal (p : ℕ) : T (D^[p] f) = (-1 : ℂ) ^ p * T f := by
    induction p with
    | zero => simp
    | succ p ih =>
      have he := hId (D^[p] f)
      rw [map_add] at he
      change T (D^[p] f) + T (D (D^[p] f)) = 0 at he
      rw [Function.iterate_succ_apply', eq_neg_of_add_eq_zero_right he, ih, pow_succ']
      ring
  have he := hVal q
  rw [hg] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ (by norm_num))

end Langlands.HarmonicAnalysis
