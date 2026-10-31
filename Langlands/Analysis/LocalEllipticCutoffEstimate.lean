import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateStatement
import Langlands.Analysis.EuclideanBallCutoff
import Langlands.Analysis.SmoothIteratedFDerivSymm

/-!
# Cutoff estimates for constant-coefficient elliptic operators on nested balls

On `EuclideanSpace ℝ (Fin d)` with its standard basis `e` and volume, let
`constCoeffAction a F x = ∑_w a w * D^r F x (e ∘ w)` be a constant-coefficient operator of
order `r` and let `derivWordNorm j F x = √(∑_w ‖D^j F x (e ∘ w)‖²)` be the Euclidean norm of the
ordered tensor of `j`-th derivatives. Assume the a priori estimate
`‖derivWordNorm r F‖_{L²} ≤ K ‖constCoeffAction a F‖_{L²}` for smooth compactly supported `F`
supported in a ball (`ConstCoeffL2Bound`).

* `eLpNorm_derivWordNorm_ball_le` and its family form `eLpNorm_sqrt_sum_derivWordNorm_ball_le`
  localise the estimate with the cutoff `ballCutoff x₀ ρ R` (Morrey–Nirenberg, Lemma 5.2):
  the top-order norm on `ball x₀ ρ` is bounded by the operator on `ball x₀ R` plus lower-order
  norms on `ball x₀ R` with weights `(R - ρ)^{-q}`.
* `ballWeightedSeminorm_add_le` and `exists_factorial_weighted_recursion` give the recursion for
  the weighted seminorms `⨆_{R/2 ≤ ρ < R} (R - ρ)^m ‖·‖_{L²(ball x₀ ρ)}` of the derivatives of
  a smooth function (Morrey–Nirenberg, Lemma 5.3).

All norms are extended (`ℝ≥0∞`); the weighted seminorms may be infinite.
-/

noncomputable section

namespace Langlands.Analysis

open MeasureTheory Metric Set Filter
open scoped ContDiff Nat ENNReal Topology

/-! ### Finite sums in `ℝ≥0∞` and an `L²` identity -/

section Aux

/-- Minkowski's inequality in `ℓ²` for a finite sum of families in `ℝ≥0∞`. -/
theorem ennreal_l2_sum_le {ι κ : Type*} (t : Finset ι) (s : Finset κ) (f : κ → ι → ℝ≥0∞) :
    (∑ i ∈ t, (∑ q ∈ s, f q i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ∑ q ∈ s, (∑ i ∈ t, f q i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h2 : (0 : ℝ≥0∞) ^ (2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos two_pos
    simp [h2]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (ENNReal.Lp_add_le t (fun i => f a i) (fun i => ∑ q ∈ s, f q i) one_le_two).trans
      (add_le_add le_rfl ih)

/-- Scaling in `ℓ²` for families in `ℝ≥0∞`. -/
theorem ennreal_l2_const_mul {ι : Type*} (t : Finset ι) (c : ℝ≥0∞) (f : ι → ℝ≥0∞) :
    (∑ i ∈ t, (c * f i) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      c * (∑ i ∈ t, f i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul]
  norm_num

/-- Monotonicity of the `ℓ²` norm of families in `ℝ≥0∞`. -/
theorem ennreal_l2_mono {ι : Type*} (t : Finset ι) {f g : ι → ℝ≥0∞} (h : ∀ i ∈ t, f i ≤ g i) :
    (∑ i ∈ t, f i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ (∑ i ∈ t, g i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i hi => ENNReal.rpow_le_rpow (h i hi) (by norm_num))
    (by norm_num)

/-- The `L²` norm of the pointwise Euclidean norm of finitely many real functions is the `ℓ²`
norm of their `L²` norms. -/
theorem eLpNorm_sqrt_sum_sq {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
    (g : ι → α → ℝ) (hg : ∀ i, AEStronglyMeasurable (g i) μ) :
    eLpNorm (fun x => Real.sqrt (∑ i, g i x ^ 2)) 2 μ =
      (∑ i, eLpNorm (g i) 2 μ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hS : AEStronglyMeasurable (fun x => Real.sqrt (∑ i, g i x ^ 2)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.univ.aestronglyMeasurable_fun_sum fun i _ => (hg i).pow 2)
  have hi : ∀ i, eLpNorm (g i) 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖g i x‖ₑ ^ (2 : ℝ) ∂μ := by
    intro i
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hg i),
      ← ENNReal.rpow_mul]
    norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hS]
  simp_rw [hi]
  rw [← lintegral_finsetSum' _ fun i _ => (hg i).enorm.pow_const _]
  norm_num only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun x => ?_
  have hsum : 0 ≤ ∑ i, g i x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.enorm_of_nonneg (Real.sqrt_nonneg _),
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
    Real.sq_sqrt hsum, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    Real.rpow_two, sq_abs]

/-- The weight transfer `t^m ≤ e^{r+1} (t (p+1)/(p+2))^m` for `m ≤ r + p`. -/
theorem pow_le_exp_mul_pow_shrink {t : ℝ} (ht : 0 ≤ t) {m r p : ℕ} (hm : m ≤ r + p) :
    t ^ m ≤ Real.exp (r + 1) * (t * (p + 1) / (p + 2)) ^ m := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  have hp2 : (0 : ℝ) < p + 2 := by positivity
  have hts : t = t * (p + 1) / (p + 2) * (1 + 1 / (p + 1)) := by
    field_simp
    ring
  have h1 : (1 + 1 / ((p : ℝ) + 1)) ^ m ≤ Real.exp (r + 1) := by
    calc (1 + 1 / ((p : ℝ) + 1)) ^ m ≤ Real.exp (1 / ((p : ℝ) + 1)) ^ m := by
          gcongr
          linarith [Real.add_one_le_exp (1 / ((p : ℝ) + 1))]
      _ = Real.exp (m * (1 / ((p : ℝ) + 1))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (r + 1) := by
          refine Real.exp_le_exp.2 ?_
          rw [mul_one_div, div_le_iff₀ hp1]
          have hmr : (m : ℝ) ≤ r + p := by exact_mod_cast hm
          have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
          have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
          nlinarith
  have hs0 : 0 ≤ t * (p + 1) / (p + 2) := by positivity
  calc t ^ m = (t * (p + 1) / (p + 2)) ^ m * (1 + 1 / (p + 1)) ^ m := by
        rw [← mul_pow, ← hts]
    _ ≤ (t * (p + 1) / (p + 2)) ^ m * Real.exp (r + 1) := by gcongr
    _ = Real.exp (r + 1) * (t * (p + 1) / (p + 2)) ^ m := mul_comm _ _

/-- `(p + 2)^q (p - q)! ≤ (q + 2)^q p!` (truncated subtraction). -/
theorem pow_mul_factorial_sub_le (p q : ℕ) : (p + 2) ^ q * (p - q)! ≤ (q + 2) ^ q * p ! := by
  rcases le_or_gt q p with hqp | hpq
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hqp
    have hprod : (q + k + 2) ^ q ≤ (q + 2) ^ q * ∏ i ∈ Finset.range q, (q + k - i) := by
      rw [show (q + k + 2) ^ q = ∏ _i ∈ Finset.range q, (q + k + 2) by simp,
        show (q + 2) ^ q = ∏ _i ∈ Finset.range q, (q + 2) by simp, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod fun i hi => ?_
      have hiq := Finset.mem_range.1 hi
      have h1 : k + 1 ≤ q + k - i := by omega
      calc q + k + 2 ≤ (q + 2) * (k + 1) := by nlinarith
        _ ≤ (q + 2) * (q + k - i) := Nat.mul_le_mul_left _ h1
    rw [← Nat.factorial_mul_descFactorial hqp, Nat.descFactorial_eq_prod_range]
    calc (q + k + 2) ^ q * (q + k - q)! ≤
          (q + 2) ^ q * (∏ i ∈ Finset.range q, (q + k - i)) * (q + k - q)! :=
        Nat.mul_le_mul_right _ hprod
      _ = (q + 2) ^ q * ((q + k - q)! * ∏ i ∈ Finset.range q, (q + k - i)) := by ring
  · have h0 : p - q = 0 := by omega
    rw [h0, Nat.factorial_zero, mul_one]
    calc (p + 2) ^ q ≤ (q + 2) ^ q := Nat.pow_le_pow_left (by omega) q
      _ ≤ (q + 2) ^ q * p ! := Nat.le_mul_of_pos_right _ (Nat.factorial_pos p)

end Aux

/-! ### Ordered derivative norms, constant-coefficient operators and weighted seminorms -/

section Defs

variable {d : ℕ}

/-- The Euclidean norm `√(∑_{w : Fin j → Fin d} ‖D^j F x (e ∘ w)‖²)` of the ordered tensor of
`j`-th derivatives of `F` at `x`, where `e` is the standard basis of `EuclideanSpace ℝ (Fin d)`.
-/
def derivWordNorm (j : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  Real.sqrt (∑ w : Fin j → Fin d,
    ‖iteratedFDeriv ℝ j F x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))‖ ^ 2)

/-- The constant-coefficient operator `F ↦ ∑_{w : Fin r → Fin d} a w * D^r F (e ∘ w)` of order
`r`, written with ordered words in the standard basis `e`. -/
def constCoeffAction {r : ℕ} (a : (Fin r → Fin d) → ℂ) (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∑ w : Fin r → Fin d,
    a w * iteratedFDeriv ℝ r F x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))

/-- The weighted seminorm `⨆_{R/2 ≤ ρ < R} (R - ρ)^m ‖G‖_{L²(ball x₀ ρ)}` (extended-valued; it
may be `∞`). -/
def ballWeightedSeminorm (G : EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d))
    (R : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ⨆ ρ ∈ Ico (R / 2) R, ENNReal.ofReal ((R - ρ) ^ m) * eLpNorm G 2 (volume.restrict (ball x₀ ρ))

/-- The `L²` a priori estimate with constant `K` for `constCoeffAction a`, on smooth compactly
supported functions whose topological support lies in `S`. -/
def ConstCoeffL2Bound {r : ℕ} (a : (Fin r → Fin d) → ℂ) (K : ℝ)
    (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ F : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ S →
    eLpNorm (derivWordNorm r F) 2 volume ≤
      ENNReal.ofReal K * eLpNorm (constCoeffAction a F) 2 volume

end Defs

section Basic

variable {d r : ℕ}

theorem ConstCoeffL2Bound.mono {a : (Fin r → Fin d) → ℂ} {K : ℝ}
    {S T : Set (EuclideanSpace ℝ (Fin d))} (h : ConstCoeffL2Bound a K T) (hST : S ⊆ T) :
    ConstCoeffL2Bound a K S :=
  fun F hF hFc hFS => h F hF hFc (hFS.trans hST)

theorem ConstCoeffL2Bound.of_le {a : (Fin r → Fin d) → ℂ} {K K' : ℝ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (h : ConstCoeffL2Bound a K S) (hKK' : K ≤ K') :
    ConstCoeffL2Bound a K' S :=
  fun F hF hFc hFS => (h F hF hFc hFS).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hKK') _)

/-- The published constant-coefficient estimate, for a symbol with lower bound `c ‖ξ‖^r`, gives
`ConstCoeffL2Bound a c⁻¹ S` on every set `S`. -/
theorem constCoeffL2Bound_of_statement (hS : ConstantCoefficientEllipticL2EstimateStatement d r)
    {a : (Fin r → Fin d) → ℂ} {c : ℝ} (hc : 0 < c)
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin d),
      c * ‖ξ‖ ^ r ≤ ‖∑ w : Fin r → Fin d, a w * ∏ j : Fin r, (ξ (w j) : ℂ)‖)
    (S : Set (EuclideanSpace ℝ (Fin d))) : ConstCoeffL2Bound a c⁻¹ S :=
  fun F hF hFc _ => hS a c hc hell F hF hFc

theorem derivWordNorm_nonneg (j : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ derivWordNorm j F x :=
  Real.sqrt_nonneg _

theorem derivWordNorm_sq (j : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    derivWordNorm j F x ^ 2 = ∑ w : Fin j → Fin d,
      ‖iteratedFDeriv ℝ j F x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem norm_basisFun (i : Fin d) : ‖EuclideanSpace.basisFun (Fin d) ℝ i‖ = 1 :=
  (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.1 i

/-- The operator norm of the `j`-th derivative is at most the ordered derivative word norm. -/
theorem norm_iteratedFDeriv_le_derivWordNorm (j : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : ‖iteratedFDeriv ℝ j F x‖ ≤ derivWordNorm j F x := by
  classical
  set T := iteratedFDeriv ℝ j F x
  set e := EuclideanSpace.basisFun (Fin d) ℝ with he
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) (fun v => ?_)
  have hexp : T v = ∑ w : Fin j → Fin d, (∏ i, v i (w i)) • T (fun i => e (w i)) := by
    conv_lhs => rw [show v = fun i => ∑ k, v i k • e k from
      funext fun i => (e.sum_repr (v i)).symm]
    rw [T.map_sum]
    exact Finset.sum_congr rfl (fun w _ => T.map_smul_univ _ _)
  have hsq : ∑ w : Fin j → Fin d, (∏ i, |v i (w i)|) ^ 2 = ∏ i, ‖v i‖ ^ 2 := by
    simp_rw [← Finset.prod_pow, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs]
    rw [Finset.prod_univ_sum]
    rfl
  calc ‖T v‖ ≤ ∑ w : Fin j → Fin d, ‖(∏ i, v i (w i)) • T (fun i => e (w i))‖ := by
        rw [hexp]; exact norm_sum_le _ _
    _ = ∑ w : Fin j → Fin d, (∏ i, |v i (w i)|) * ‖T (fun i => e (w i))‖ := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    _ ≤ Real.sqrt (∑ w : Fin j → Fin d, (∏ i, |v i (w i)|) ^ 2) * derivWordNorm j F x :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = derivWordNorm j F x * ∏ i, ‖v i‖ := by
        rw [hsq, Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun i _ => norm_nonneg _),
          mul_comm]

theorem derivWordNorm_congr_of_eventuallyEq {F G : EuclideanSpace ℝ (Fin d) → ℂ}
    {x : EuclideanSpace ℝ (Fin d)} (h : F =ᶠ[𝓝 x] G) (j : ℕ) :
    derivWordNorm j F x = derivWordNorm j G x := by
  simp only [derivWordNorm, (h.iteratedFDeriv ℝ j).eq_of_nhds]

theorem continuousOn_iteratedFDeriv_of_isOpen {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : EuclideanSpace ℝ (Fin d) → F} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hU : ContDiffOn ℝ ∞ U s) (hs : IsOpen s) (j : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ j U) s :=
  (hU.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs.uniqueDiffOn).congr
    (iteratedFDerivWithin_of_isOpen j hs).symm

theorem continuousOn_derivWordNorm {U : EuclideanSpace ℝ (Fin d) → ℂ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hU : ContDiffOn ℝ ∞ U s) (hs : IsOpen s) (j : ℕ) :
    ContinuousOn (derivWordNorm j U) s := by
  have h := continuousOn_iteratedFDeriv_of_isOpen hU hs j
  unfold derivWordNorm
  refine ContinuousOn.sqrt (continuousOn_finsetSum _ fun w _ => ?_)
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) ℂ
    (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))).continuous.comp_continuousOn h).norm.pow 2

theorem continuousOn_constCoeffAction {a : (Fin r → Fin d) → ℂ}
    {U : EuclideanSpace ℝ (Fin d) → ℂ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hU : ContDiffOn ℝ ∞ U s) (hs : IsOpen s) : ContinuousOn (constCoeffAction a U) s := by
  have h := continuousOn_iteratedFDeriv_of_isOpen hU hs r
  unfold constCoeffAction
  exact continuousOn_finsetSum _ fun w _ => continuousOn_const.mul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => EuclideanSpace ℝ (Fin d)) ℂ
      (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))).continuous.comp_continuousOn h)

theorem le_ballWeightedSeminorm {G : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} {R ρ : ℝ} (m : ℕ) (hρ : ρ ∈ Ico (R / 2) R) :
    ENNReal.ofReal ((R - ρ) ^ m) * eLpNorm G 2 (volume.restrict (ball x₀ ρ)) ≤
      ballWeightedSeminorm G x₀ R m := by
  unfold ballWeightedSeminorm
  exact le_iSup₂_of_le ρ hρ le_rfl

end Basic

/-! ### The Leibniz commutator of the cutoff -/

section Leibniz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x₀ : E} {ρ R : ℝ}

/-- The Leibniz formula for `ballCutoff x₀ ρ R • U` without its zeroth-order term
`ballCutoff x₀ ρ R x • D^k U x`: at points of `ball x₀ R`, for `U` smooth on that ball, the
remainder involves only derivatives of order `≥ 1` of the cutoff. -/
theorem norm_iteratedFDeriv_ballCutoff_smul_sub_le {U : E → F} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (hU : ContDiffOn ℝ ∞ U (ball x₀ R)) {x : E} (hx : x ∈ ball x₀ R) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => ballCutoff x₀ ρ R y • U y) x -
        ballCutoff x₀ ρ R x • iteratedFDeriv ℝ k U x‖ ≤
      ∑ i ∈ Finset.Icc 1 k, (k.choose i : ℝ) * (ballCutoffConst i / (R - ρ) ^ i) *
        ‖iteratedFDeriv ℝ (k - i) U x‖ := by
  set ζ := ballCutoff x₀ ρ R with hζdef
  set c := ζ x with hc
  have hs : IsOpen (ball x₀ R) := isOpen_ball
  have hζ : ContDiff ℝ ∞ ζ := contDiff_ballCutoff x₀ ρ R
  have hUx : ContDiffAt ℝ ∞ U x := hU.contDiffAt (hs.mem_nhds hx)
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have key : iteratedFDeriv ℝ k (fun y => ζ y • U y) x - c • iteratedFDeriv ℝ k U x =
      iteratedFDeriv ℝ k (fun y => (ζ y - c) • U y) x := by
    have h1 : (fun y => (ζ y - c) • U y) = (fun y => ζ y • U y) - (fun y => c • U y) := by
      funext y; simp [sub_smul]
    rw [h1, iteratedFDeriv_sub_apply (f := fun y => ζ y • U y) (g := fun y => c • U y)
      ((hζ.contDiffAt.smul hUx).of_le hk)
      ((hUx.const_smul c).of_le hk), iteratedFDeriv_const_smul_apply' (hUx.of_le hk)]
  rw [key]
  have hg : ContDiffOn ℝ ∞ (fun y => ζ y - c) (ball x₀ R) := (hζ.sub contDiff_const).contDiffOn
  have h := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) hg hU hs.uniqueDiffOn hx (n := k) hk
  rw [iteratedFDerivWithin_of_isOpen k hs hx] at h
  refine h.trans ?_
  rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos k), Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc]
  have h0 : ‖iteratedFDerivWithin ℝ 0 (fun y => ζ y - c) (ball x₀ R) x‖ = 0 := by
    rw [norm_iteratedFDerivWithin_zero]; simp [hc]
  rw [h0, mul_zero, zero_mul, zero_add]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : i ≠ 0 := by
    have := (Finset.mem_Icc.1 hi).1
    omega
  rw [iteratedFDerivWithin_of_isOpen i hs hx, iteratedFDerivWithin_of_isOpen (k - i) hs hx]
  have hD : iteratedFDeriv ℝ i (fun y => ζ y - c) x = iteratedFDeriv ℝ i ζ x := by
    rw [show (fun y => ζ y - c) = ζ - fun _ => c from rfl,
      iteratedFDeriv_sub_apply (hζ.contDiffAt.of_le (by exact_mod_cast le_top))
        contDiffAt_const, iteratedFDeriv_const_of_ne hi1, Pi.zero_apply, sub_zero]
  rw [hD]
  gcongr
  exact norm_iteratedFDeriv_ballCutoff_le hρ hρR i x

end Leibniz

/-! ### Morrey–Nirenberg Lemma 5.2: the localised estimate -/

section Cutoff

variable {d r : ℕ} {a : (Fin r → Fin d) → ℂ} {K : ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
  {ρ R : ℝ}

/-- Pointwise commutator bound: on `ball x₀ R`, the operator applied to the cutoff product is
bounded by the operator applied to `U` plus lower-order derivative norms of `U`. -/
theorem norm_constCoeffAction_ballCutoff_smul_le {U : EuclideanSpace ℝ (Fin d) → ℂ}
    (hρ : 0 ≤ ρ) (hρR : ρ < R) (hU : ContDiffOn ℝ ∞ U (ball x₀ R))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball x₀ R) :
    ‖constCoeffAction a (fun y => ballCutoff x₀ ρ R y • U y) x‖ ≤
      ‖constCoeffAction a U x‖ + ∑ q ∈ Finset.Icc 1 r,
        (∑ w, ‖a w‖) * (r.choose q : ℝ) * (ballCutoffConst q / (R - ρ) ^ q) *
          derivWordNorm (r - q) U x := by
  set ζ := ballCutoff x₀ ρ R with hζdef
  set e := EuclideanSpace.basisFun (Fin d) ℝ with he
  set T := iteratedFDeriv ℝ r (fun y => ζ y • U y) x - ζ x • iteratedFDeriv ℝ r U x with hT
  have hδ : 0 < R - ρ := sub_pos.2 hρR
  have hsplit : constCoeffAction a (fun y => ζ y • U y) x =
      (ζ x : ℂ) * constCoeffAction a U x + ∑ w : Fin r → Fin d, a w * T (fun i => e (w i)) := by
    simp only [constCoeffAction, hT, sub_apply,
      smul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Complex.real_smul]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ballCutoff_nonneg x₀ ρ R x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (ballCutoff_le_one x₀ ρ R x)
  · have hTe : ∀ w : Fin r → Fin d, ‖T (fun i => e (w i))‖ ≤ ‖T‖ := fun w => by
      refine (T.le_opNorm _).trans (le_of_eq ?_)
      simp [he]
    have hc0 : ∀ q, 0 ≤ (r.choose q : ℝ) * (ballCutoffConst q / (R - ρ) ^ q) := fun q =>
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (ballCutoffConst_nonneg q) (pow_nonneg hδ.le q))
    calc ‖∑ w : Fin r → Fin d, a w * T (fun i => e (w i))‖ ≤ ∑ w, ‖a w‖ * ‖T‖ :=
          norm_sum_le_of_le _ fun w _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hTe w) (norm_nonneg _)
      _ = (∑ w, ‖a w‖) * ‖T‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ w, ‖a w‖) * ∑ q ∈ Finset.Icc 1 r, (r.choose q : ℝ) *
            (ballCutoffConst q / (R - ρ) ^ q) * ‖iteratedFDeriv ℝ (r - q) U x‖ :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_ballCutoff_smul_sub_le hρ hρR hU hx r)
            (Finset.sum_nonneg fun w _ => norm_nonneg _)
      _ ≤ (∑ w, ‖a w‖) * ∑ q ∈ Finset.Icc 1 r, (r.choose q : ℝ) *
            (ballCutoffConst q / (R - ρ) ^ q) * derivWordNorm (r - q) U x := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_)
            (Finset.sum_nonneg fun w _ => norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_derivWordNorm _ _ _) (hc0 q)
      _ = ∑ q ∈ Finset.Icc 1 r, (∑ w, ‖a w‖) * (r.choose q : ℝ) *
            (ballCutoffConst q / (R - ρ) ^ q) * derivWordNorm (r - q) U x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring

/-- **Morrey–Nirenberg Lemma 5.2 (scalar form).** If the constant-coefficient estimate holds for
functions supported in `ball x₀ R` and `U` is smooth on `ball x₀ R`, then for `0 ≤ ρ < R`
the `L²(ball x₀ ρ)` norm of the order-`r` derivative word norm of `U` is bounded by `K` times
the `L²(ball x₀ R)` norm of `constCoeffAction a U` plus lower-order terms on `ball x₀ R` with
weights `(R - ρ)^{-q}`. -/
theorem eLpNorm_derivWordNorm_ball_le (hP : ConstCoeffL2Bound a K (ball x₀ R)) (hρ : 0 ≤ ρ)
    (hρR : ρ < R) {U : EuclideanSpace ℝ (Fin d) → ℂ} (hU : ContDiffOn ℝ ∞ U (ball x₀ R)) :
    eLpNorm (derivWordNorm r U) 2 (volume.restrict (ball x₀ ρ)) ≤
      ENNReal.ofReal K * eLpNorm (constCoeffAction a U) 2 (volume.restrict (ball x₀ R)) +
        ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (K * ((∑ w, ‖a w‖) * (r.choose q : ℝ) *
            (ballCutoffConst q / (R - ρ) ^ q))) *
          eLpNorm (derivWordNorm (r - q) U) 2 (volume.restrict (ball x₀ R)) := by
  set ζ := ballCutoff x₀ ρ R with hζdef
  set F : EuclideanSpace ℝ (Fin d) → ℂ := fun y => ζ y • U y with hFdef
  set c : ℕ → ℝ := fun q => (∑ w, ‖a w‖) * (r.choose q : ℝ) * (ballCutoffConst q / (R - ρ) ^ q)
    with hcdef
  have hδ : 0 < R - ρ := sub_pos.2 hρR
  have hc0 : ∀ q, 0 ≤ c q := fun q =>
    mul_nonneg (mul_nonneg (Finset.sum_nonneg fun w _ => norm_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (ballCutoffConst_nonneg q) (pow_nonneg hδ.le q))
  have hFs : ContDiff ℝ ∞ F := contDiff_ballCutoff_smul hρ hρR hU
  have hFc : HasCompactSupport F := hasCompactSupport_ballCutoff_smul U hρ hρR
  have hFt : tsupport F ⊆ ball x₀ R :=
    (tsupport_ballCutoff_smul_subset U hρ hρR).trans (closedBall_subset_ball (by linarith))
  have h1 : eLpNorm (derivWordNorm r U) 2 (volume.restrict (ball x₀ ρ)) =
      eLpNorm (derivWordNorm r F) 2 (volume.restrict (ball x₀ ρ)) := by
    refine eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_)
    exact (derivWordNorm_congr_of_eventuallyEq (ballCutoff_smul_eventuallyEq U hρ hρR hx) r).symm
  have hPF : Continuous (constCoeffAction a F) := by
    unfold constCoeffAction
    exact continuous_finsetSum _ fun w _ => continuous_const.mul
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => EuclideanSpace ℝ (Fin d)) ℂ
        (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))).continuous.comp
        (hFs.continuous_iteratedFDeriv (by exact_mod_cast le_top)))
  have h4 : eLpNorm (constCoeffAction a F) 2 volume =
      eLpNorm (constCoeffAction a F) 2 (volume.restrict (ball x₀ R)) := by
    refine (eLpNorm_restrict_eq_of_support_subset hPF.aestronglyMeasurable ?_).symm
    intro x hx
    by_contra hxR
    apply hx
    have hD : iteratedFDeriv ℝ r F x = 0 := by
      by_contra hne
      exact hxR (hFt (support_iteratedFDeriv_subset r hne))
    simp [constCoeffAction, hD]
  have hmU : ∀ j, AEStronglyMeasurable (derivWordNorm j U) (volume.restrict (ball x₀ R)) :=
    fun j => (continuousOn_derivWordNorm hU isOpen_ball j).aestronglyMeasurable measurableSet_ball
  have hmPU : AEStronglyMeasurable (constCoeffAction a U) (volume.restrict (ball x₀ R)) :=
    (continuousOn_constCoeffAction hU isOpen_ball).aestronglyMeasurable measurableSet_ball
  have h5 : eLpNorm (constCoeffAction a F) 2 (volume.restrict (ball x₀ R)) ≤
      eLpNorm (constCoeffAction a U) 2 (volume.restrict (ball x₀ R)) +
        ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (c q) *
          eLpNorm (derivWordNorm (r - q) U) 2 (volume.restrict (ball x₀ R)) := by
    calc eLpNorm (constCoeffAction a F) 2 (volume.restrict (ball x₀ R))
        ≤ eLpNorm (fun x => ‖constCoeffAction a U x‖ +
            ∑ q ∈ Finset.Icc 1 r, c q * derivWordNorm (r - q) U x) 2
            (volume.restrict (ball x₀ R)) := by
          refine eLpNorm_mono_ae_real hPF.aestronglyMeasurable
            (ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_)
          exact norm_constCoeffAction_ballCutoff_smul_le hρ hρR hU hx
      _ ≤ eLpNorm (fun x => ‖constCoeffAction a U x‖) 2 (volume.restrict (ball x₀ R)) +
            eLpNorm (∑ q ∈ Finset.Icc 1 r, fun x => c q * derivWordNorm (r - q) U x) 2
              (volume.restrict (ball x₀ R)) := by
          have hfun : (fun x => ‖constCoeffAction a U x‖ +
              ∑ q ∈ Finset.Icc 1 r, c q * derivWordNorm (r - q) U x) =
              (fun x => ‖constCoeffAction a U x‖) +
                ∑ q ∈ Finset.Icc 1 r, fun x => c q * derivWordNorm (r - q) U x := by
            funext x
            simp [Finset.sum_apply]
          rw [hfun]
          exact eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (constCoeffAction a U) 2 (volume.restrict (ball x₀ R)) +
            ∑ q ∈ Finset.Icc 1 r, eLpNorm (fun x => c q * derivWordNorm (r - q) U x) 2
              (volume.restrict (ball x₀ R)) := by
          rw [eLpNorm_norm _ hmPU]
          exact add_le_add le_rfl (eLpNorm_sum_le (by norm_num))
      _ = eLpNorm (constCoeffAction a U) 2 (volume.restrict (ball x₀ R)) +
            ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (c q) *
              eLpNorm (derivWordNorm (r - q) U) 2 (volume.restrict (ball x₀ R)) := by
          congr 1
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [show (fun x => c q * derivWordNorm (r - q) U x) = c q • derivWordNorm (r - q) U
            from rfl, eLpNorm_const_smul, Real.enorm_of_nonneg (hc0 q)]
  calc eLpNorm (derivWordNorm r U) 2 (volume.restrict (ball x₀ ρ))
      = eLpNorm (derivWordNorm r F) 2 (volume.restrict (ball x₀ ρ)) := h1
    _ ≤ eLpNorm (derivWordNorm r F) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ ENNReal.ofReal K * eLpNorm (constCoeffAction a F) 2 volume := hP F hFs hFc hFt
    _ = ENNReal.ofReal K * eLpNorm (constCoeffAction a F) 2 (volume.restrict (ball x₀ R)) := by
        rw [h4]
    _ ≤ ENNReal.ofReal K * (eLpNorm (constCoeffAction a U) 2 (volume.restrict (ball x₀ R)) +
          ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (c q) *
            eLpNorm (derivWordNorm (r - q) U) 2 (volume.restrict (ball x₀ R))) :=
        mul_le_mul' le_rfl h5
    _ = _ := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul' (hc0 q)]

/-- **Morrey–Nirenberg Lemma 5.2 (family form).** The estimate of
`eLpNorm_derivWordNorm_ball_le` for a finite family `U i` of functions smooth on `ball x₀ R`,
with the pointwise Euclidean norms `√(∑_i ·²)` of the family. -/
theorem eLpNorm_sqrt_sum_derivWordNorm_ball_le {ι : Type*} [Fintype ι]
    (hP : ConstCoeffL2Bound a K (ball x₀ R)) (hρ : 0 ≤ ρ) (hρR : ρ < R)
    {U : ι → EuclideanSpace ℝ (Fin d) → ℂ} (hU : ∀ i, ContDiffOn ℝ ∞ (U i) (ball x₀ R)) :
    eLpNorm (fun x => Real.sqrt (∑ i, derivWordNorm r (U i) x ^ 2)) 2
        (volume.restrict (ball x₀ ρ)) ≤
      ENNReal.ofReal K * eLpNorm (fun x => Real.sqrt (∑ i, ‖constCoeffAction a (U i) x‖ ^ 2)) 2
          (volume.restrict (ball x₀ R)) +
        ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (K * ((∑ w, ‖a w‖) * (r.choose q : ℝ) *
            (ballCutoffConst q / (R - ρ) ^ q))) *
          eLpNorm (fun x => Real.sqrt (∑ i, derivWordNorm (r - q) (U i) x ^ 2)) 2
            (volume.restrict (ball x₀ R)) := by
  set cq : ℕ → ℝ≥0∞ := fun q => ENNReal.ofReal (K * ((∑ w, ‖a w‖) * (r.choose q : ℝ) *
    (ballCutoffConst q / (R - ρ) ^ q))) with hcq
  have hmρ : ∀ j i, AEStronglyMeasurable (derivWordNorm j (U i)) (volume.restrict (ball x₀ ρ)) :=
    fun j i => ((continuousOn_derivWordNorm (hU i) isOpen_ball j).mono
      (ball_subset_ball hρR.le)).aestronglyMeasurable measurableSet_ball
  have hmR : ∀ j i, AEStronglyMeasurable (derivWordNorm j (U i)) (volume.restrict (ball x₀ R)) :=
    fun j i => (continuousOn_derivWordNorm (hU i) isOpen_ball j).aestronglyMeasurable
      measurableSet_ball
  have hmP : ∀ i, AEStronglyMeasurable (constCoeffAction a (U i))
      (volume.restrict (ball x₀ R)) := fun i =>
    (continuousOn_constCoeffAction (hU i) isOpen_ball).aestronglyMeasurable measurableSet_ball
  rw [eLpNorm_sqrt_sum_sq _ (hmρ r),
    eLpNorm_sqrt_sum_sq (fun i x => ‖constCoeffAction a (U i) x‖) fun i => (hmP i).norm]
  have eqq : ∀ q, eLpNorm (fun x => Real.sqrt (∑ i, derivWordNorm (r - q) (U i) x ^ 2)) 2
      (volume.restrict (ball x₀ R)) =
      (∑ i, eLpNorm (derivWordNorm (r - q) (U i)) 2 (volume.restrict (ball x₀ R)) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) := fun q => eLpNorm_sqrt_sum_sq _ (hmR (r - q))
  rw [Finset.sum_congr rfl fun q (_ : q ∈ Finset.Icc 1 r) => by rw [eqq q]]
  have hi : ∀ i, eLpNorm (derivWordNorm r (U i)) 2 (volume.restrict (ball x₀ ρ)) ≤
      ENNReal.ofReal K * eLpNorm (fun x => ‖constCoeffAction a (U i) x‖) 2
          (volume.restrict (ball x₀ R)) +
        ∑ q ∈ Finset.Icc 1 r, cq q *
          eLpNorm (derivWordNorm (r - q) (U i)) 2 (volume.restrict (ball x₀ R)) := by
    intro i
    rw [eLpNorm_norm _ (hmP i)]
    exact eLpNorm_derivWordNorm_ball_le hP hρ hρR (hU i)
  calc (∑ i, eLpNorm (derivWordNorm r (U i)) 2 (volume.restrict (ball x₀ ρ)) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ)
      ≤ (∑ i, (ENNReal.ofReal K * eLpNorm (fun x => ‖constCoeffAction a (U i) x‖) 2
            (volume.restrict (ball x₀ R)) + ∑ q ∈ Finset.Icc 1 r, cq q *
            eLpNorm (derivWordNorm (r - q) (U i)) 2 (volume.restrict (ball x₀ R))) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := ennreal_l2_mono _ fun i _ => hi i
    _ ≤ (∑ i, (ENNReal.ofReal K * eLpNorm (fun x => ‖constCoeffAction a (U i) x‖) 2
            (volume.restrict (ball x₀ R))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
          (∑ i, (∑ q ∈ Finset.Icc 1 r, cq q *
            eLpNorm (derivWordNorm (r - q) (U i)) 2 (volume.restrict (ball x₀ R))) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := ENNReal.Lp_add_le _ _ _ one_le_two
    _ ≤ _ := by
        rw [ennreal_l2_const_mul]
        refine add_le_add le_rfl ((ennreal_l2_sum_le _ _ _).trans (le_of_eq ?_))
        exact Finset.sum_congr rfl fun q _ => ennreal_l2_const_mul _ _ _

end Cutoff

/-! ### Regrouping derivative words -/

section Words

variable {d r : ℕ}

theorem append_basisFun {j p : ℕ} (w : Fin j → Fin d) (w' : Fin p → Fin d) :
    Fin.append (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))
        (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i)) =
      fun i => EuclideanSpace.basisFun (Fin d) ℝ (Fin.append w w' i) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right i => simp

/-- Regrouping words: the squared word norms of order `j` of the line derivatives of `u` along
all basis words `w'` of length `p` add up to the squared word norm of order `j + p` of `u`. -/
theorem sum_sq_derivWordNorm_iteratedLineDeriv {u : EuclideanSpace ℝ (Fin d) → ℂ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) (j p : ℕ) :
    ∑ w' : Fin p → Fin d, derivWordNorm j
        (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x ^ 2 =
      derivWordNorm (j + p) u x ^ 2 := by
  simp_rw [derivWordNorm_sq]
  have h : ∀ (w : Fin j → Fin d) (w' : Fin p → Fin d),
      iteratedFDeriv ℝ j
          (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x
          (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i)) =
        iteratedFDeriv ℝ (j + p) u x
          (fun i => EuclideanSpace.basisFun (Fin d) ℝ (Fin.append w w' i)) := by
    intro w w'
    rw [← append_basisFun]
    exact iteratedLineDeriv_iteratedLineDeriv hu hs hx (by exact_mod_cast le_top) _ _
  simp_rw [h]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact (Fin.appendEquiv j p).sum_comp
    (fun W => ‖iteratedFDeriv ℝ (j + p) u x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (W i))‖ ^ 2)

theorem sqrt_sum_sq_derivWordNorm_iteratedLineDeriv {u : EuclideanSpace ℝ (Fin d) → ℂ}
    {s : Set (EuclideanSpace ℝ (Fin d))} (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) (j p : ℕ) :
    Real.sqrt (∑ w' : Fin p → Fin d, derivWordNorm j
        (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x ^ 2) =
      derivWordNorm (j + p) u x := by
  rw [sum_sq_derivWordNorm_iteratedLineDeriv hu hs hx, Real.sqrt_sq (derivWordNorm_nonneg _ _ _)]

/-- The constant-coefficient operator commutes with line derivatives of smooth functions (by the
symmetry of iterated derivatives). -/
theorem constCoeffAction_iteratedLineDeriv {a : (Fin r → Fin d) → ℂ}
    {u : EuclideanSpace ℝ (Fin d) → ℂ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s)
    {p : ℕ} (w' : Fin p → Fin d) :
    constCoeffAction a
        (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x =
      iteratedFDeriv ℝ p (constCoeffAction a u) x
        (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i)) := by
  have hg : ∀ w : Fin r → Fin d, ContDiffAt ℝ ∞
      (iteratedLineDeriv ℝ r u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i))) x :=
    fun w => (contDiffOn_infty_iteratedLineDeriv hu hs _).contDiffAt (hs.mem_nhds hx)
  have hp : ((p : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hfun : constCoeffAction a u = fun y => ∑ w : Fin r → Fin d,
      a w • iteratedLineDeriv ℝ r u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i)) y := rfl
  rw [hfun, iteratedFDeriv_fun_sum_apply
    (f := fun w y => a w • iteratedLineDeriv ℝ r u
      (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i)) y)
    (fun w _ => ((hg w).const_smul (a w)).of_le hp)]
  simp only [sum_apply]
  unfold constCoeffAction
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [iteratedFDeriv_const_smul_apply' ((hg w).of_le hp), smul_apply,
    smul_eq_mul]
  congr 1
  change iteratedLineDeriv ℝ r (iteratedLineDeriv ℝ p u _) _ x =
    iteratedLineDeriv ℝ p (iteratedLineDeriv ℝ r u _) _ x
  rw [iteratedLineDeriv_iteratedLineDeriv hu hs hx (by exact_mod_cast le_top),
    iteratedLineDeriv_iteratedLineDeriv hu hs hx (by exact_mod_cast le_top)]
  exact iteratedFDeriv_append_comm_of_contDiffAt (hu.contDiffAt (hs.mem_nhds hx))
    (by exact_mod_cast le_top) _ _

theorem sqrt_sum_sq_norm_constCoeffAction_iteratedLineDeriv {a : (Fin r → Fin d) → ℂ}
    {u : EuclideanSpace ℝ (Fin d) → ℂ} {s : Set (EuclideanSpace ℝ (Fin d))}
    (hu : ContDiffOn ℝ ∞ u s) (hs : IsOpen s) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s)
    (p : ℕ) :
    Real.sqrt (∑ w' : Fin p → Fin d, ‖constCoeffAction a
        (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x‖ ^ 2) =
      derivWordNorm p (constCoeffAction a u) x := by
  simp_rw [constCoeffAction_iteratedLineDeriv hu hs hx]
  rfl

end Words

/-! ### Morrey–Nirenberg Lemma 5.3: the weighted recursion -/

section Weighted

variable {d r : ℕ} {a : (Fin r → Fin d) → ℂ} {K : ℝ} {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ}

/-- **Weighted recursion (unnormalised).** For `u` smooth on `ball x₀ R` and the
estimate on `ball x₀ R` with `K ≥ 0`, the weighted seminorm of the order-`r + p` derivative
word norm is bounded by that of `D^p (constCoeffAction a u)` and those of the orders
`r + p - q`, `1 ≤ q ≤ r`, with factors `(p + 2)^q`. -/
theorem ballWeightedSeminorm_add_le (hK : 0 ≤ K)
    {u : EuclideanSpace ℝ (Fin d) → ℂ} (hu : ContDiffOn ℝ ∞ u (ball x₀ R))
    (hP : ConstCoeffL2Bound a K (ball x₀ R)) (p : ℕ) :
    ballWeightedSeminorm (derivWordNorm (r + p) u) x₀ R (r + p) ≤
      ENNReal.ofReal (Real.exp (r + 1) * K) *
          ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p) +
        ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (Real.exp (r + 1) * K *
            ((∑ w, ‖a w‖) * (r.choose q : ℝ) * ballCutoffConst q) * ((p : ℝ) + 2) ^ q) *
          ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q) := by
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨hρ1, hρ2⟩ := hρ
  set t := R - ρ with ht
  have ht0 : 0 < t := sub_pos.2 hρ2
  have hp2 : (0 : ℝ) < p + 2 := by positivity
  set ρ' := ρ + t / (p + 2) with hρ'
  have hδpos : 0 < t / (p + 2) := div_pos ht0 hp2
  have hρρ' : ρ < ρ' := by linarith
  have hδt : t / (p + 2) < t := div_lt_self ht0 (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
  have hρ'R : ρ' < R := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ'mem : ρ' ∈ Ico (R / 2) R := ⟨by linarith, hρ'R⟩
  have hs : R - ρ' = t * (p + 1) / (p + 2) := by
    rw [hρ']
    field_simp
    ring
  have hδ : ρ' - ρ = t / (p + 2) := by rw [hρ']; ring
  have hball : ball x₀ ρ' ⊆ ball x₀ R := ball_subset_ball hρ'R.le
  have hU : ∀ w' : Fin p → Fin d, ContDiffOn ℝ ∞
      (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i)))
      (ball x₀ ρ') := fun w' => (contDiffOn_infty_iteratedLineDeriv hu isOpen_ball _).mono hball
  have hfam := eLpNorm_sqrt_sum_derivWordNorm_ball_le (hP.mono hball) hρ0 hρρ' hU
  have eq1 : eLpNorm (fun x => Real.sqrt (∑ w' : Fin p → Fin d, derivWordNorm r
        (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x ^ 2)) 2
        (volume.restrict (ball x₀ ρ)) =
      eLpNorm (derivWordNorm (r + p) u) 2 (volume.restrict (ball x₀ ρ)) :=
    eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun x hx =>
      sqrt_sum_sq_derivWordNorm_iteratedLineDeriv hu isOpen_ball
        (ball_subset_ball hρ2.le hx) r p)
  have eq2 : eLpNorm (fun x => Real.sqrt (∑ w' : Fin p → Fin d, ‖constCoeffAction a
        (iteratedLineDeriv ℝ p u (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x‖ ^ 2)) 2
        (volume.restrict (ball x₀ ρ')) =
      eLpNorm (derivWordNorm p (constCoeffAction a u)) 2 (volume.restrict (ball x₀ ρ')) :=
    eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun x hx =>
      sqrt_sum_sq_norm_constCoeffAction_iteratedLineDeriv hu isOpen_ball (hball hx) p)
  have eq3 : ∀ q ∈ Finset.Icc 1 r, eLpNorm (fun x => Real.sqrt (∑ w' : Fin p → Fin d,
        derivWordNorm (r - q) (iteratedLineDeriv ℝ p u
          (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w' i))) x ^ 2)) 2
        (volume.restrict (ball x₀ ρ')) =
      eLpNorm (derivWordNorm (r + p - q) u) 2 (volume.restrict (ball x₀ ρ')) := by
    intro q hq
    have hqr := (Finset.mem_Icc.1 hq).2
    refine eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_)
    dsimp only
    rw [sqrt_sum_sq_derivWordNorm_iteratedLineDeriv hu isOpen_ball (hball hx) (r - q) p,
      show r - q + p = r + p - q by omega]
  rw [eq1, eq2, Finset.sum_congr rfl fun q hq => by rw [eq3 q hq]] at hfam
  set A := ∑ w, ‖a w‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun w _ => norm_nonneg _
  have hE0 : 0 ≤ Real.exp (r + 1) := (Real.exp_pos _).le
  calc ENNReal.ofReal (t ^ (r + p)) *
        eLpNorm (derivWordNorm (r + p) u) 2 (volume.restrict (ball x₀ ρ))
      ≤ ENNReal.ofReal (t ^ (r + p)) * (ENNReal.ofReal K *
          eLpNorm (derivWordNorm p (constCoeffAction a u)) 2 (volume.restrict (ball x₀ ρ')) +
          ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (K * (A * (r.choose q : ℝ) *
            (ballCutoffConst q / (ρ' - ρ) ^ q))) *
            eLpNorm (derivWordNorm (r + p - q) u) 2 (volume.restrict (ball x₀ ρ'))) :=
        mul_le_mul' le_rfl hfam
    _ = ENNReal.ofReal (t ^ (r + p) * K) *
          eLpNorm (derivWordNorm p (constCoeffAction a u)) 2 (volume.restrict (ball x₀ ρ')) +
          ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (t ^ (r + p) * (K * (A * (r.choose q : ℝ) *
            (ballCutoffConst q / (ρ' - ρ) ^ q)))) *
            eLpNorm (derivWordNorm (r + p - q) u) 2 (volume.restrict (ball x₀ ρ')) := by
        rw [mul_add, Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine add_le_add ?_ (Finset.sum_le_sum fun q hq => ?_)
        · calc ENNReal.ofReal (t ^ (r + p) * K) *
                eLpNorm (derivWordNorm p (constCoeffAction a u)) 2 (volume.restrict (ball x₀ ρ'))
              ≤ ENNReal.ofReal (Real.exp (r + 1) * K * (R - ρ') ^ (r + p)) *
                eLpNorm (derivWordNorm p (constCoeffAction a u)) 2
                  (volume.restrict (ball x₀ ρ')) := by
                refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
                rw [hs]
                calc t ^ (r + p) * K
                    ≤ Real.exp (r + 1) * (t * (p + 1) / (p + 2)) ^ (r + p) * K :=
                      mul_le_mul_of_nonneg_right
                        (pow_le_exp_mul_pow_shrink ht0.le le_rfl) hK
                  _ = Real.exp (r + 1) * K * (t * (p + 1) / (p + 2)) ^ (r + p) := by ring
            _ = ENNReal.ofReal (Real.exp (r + 1) * K) * (ENNReal.ofReal ((R - ρ') ^ (r + p)) *
                eLpNorm (derivWordNorm p (constCoeffAction a u)) 2
                  (volume.restrict (ball x₀ ρ'))) := by
                rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
            _ ≤ _ := mul_le_mul' le_rfl (le_ballWeightedSeminorm _ hρ'mem)
        · have hqr := (Finset.mem_Icc.1 hq).2
          set B := Real.exp (r + 1) * K * (A * (r.choose q : ℝ) * ballCutoffConst q) *
            ((p : ℝ) + 2) ^ q with hB
          have hB0 : 0 ≤ B := by
            have := ballCutoffConst_nonneg q
            positivity
          calc ENNReal.ofReal (t ^ (r + p) * (K * (A * (r.choose q : ℝ) *
                (ballCutoffConst q / (ρ' - ρ) ^ q)))) *
                eLpNorm (derivWordNorm (r + p - q) u) 2 (volume.restrict (ball x₀ ρ'))
              ≤ ENNReal.ofReal (B * (R - ρ') ^ (r + p - q)) *
                eLpNorm (derivWordNorm (r + p - q) u) 2 (volume.restrict (ball x₀ ρ')) := by
                refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
                rw [hs, hδ]
                have hpow : t ^ (r + p) = t ^ (r + p - q) * t ^ q := by
                  rw [← pow_add]
                  congr 1
                  omega
                have hshr := pow_le_exp_mul_pow_shrink ht0.le (m := r + p - q) (r := r) (p := p)
                  (by omega)
                have hB' : 0 ≤ K * (A * (r.choose q : ℝ) * ballCutoffConst q) *
                    ((p : ℝ) + 2) ^ q := by
                  have := ballCutoffConst_nonneg q
                  positivity
                calc t ^ (r + p) * (K * (A * (r.choose q : ℝ) *
                      (ballCutoffConst q / (t / (p + 2)) ^ q)))
                    = K * (A * (r.choose q : ℝ) * ballCutoffConst q) * ((p : ℝ) + 2) ^ q *
                        t ^ (r + p - q) := by
                      rw [hpow, div_pow]
                      field_simp
                  _ ≤ K * (A * (r.choose q : ℝ) * ballCutoffConst q) * ((p : ℝ) + 2) ^ q *
                        (Real.exp (r + 1) * (t * (p + 1) / (p + 2)) ^ (r + p - q)) :=
                      mul_le_mul_of_nonneg_left hshr hB'
                  _ = B * (t * (p + 1) / (p + 2)) ^ (r + p - q) := by rw [hB]; ring
            _ = ENNReal.ofReal B * (ENNReal.ofReal ((R - ρ') ^ (r + p - q)) *
                eLpNorm (derivWordNorm (r + p - q) u) 2 (volume.restrict (ball x₀ ρ'))) := by
                rw [ENNReal.ofReal_mul hB0, mul_assoc]
            _ ≤ _ := mul_le_mul' le_rfl (le_ballWeightedSeminorm _ hρ'mem)

/-- **Morrey–Nirenberg Lemma 5.3 (factorial normalisation).** For fixed `d`, `r`, `a`, `K` there
is `K₃ > 0` such that for every centre `x₀`, radius `R`, function `u` smooth on `ball x₀ R`
for which the estimate `ConstCoeffL2Bound a K (ball x₀ R)` holds, and every `p`,
`N(r + p) / p! ≤ K₃ (M(p) / p! + ∑_{q = 1}^{r} N(r + p - q) / (p - q)!)`, where `N(m)` is the
weighted seminorm of the order-`m` derivative word norm of `u` with weight exponent `m`, `M(p)`
that of the order-`p` derivative word norm of `constCoeffAction a u` with weight exponent
`r + p`, and `p - q` is truncated subtraction. -/
theorem exists_factorial_weighted_recursion (a : (Fin r → Fin d) → ℂ) (K : ℝ) :
    ∃ K₃ : ℝ, 0 < K₃ ∧ ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ)
      (u : EuclideanSpace ℝ (Fin d) → ℂ), ContDiffOn ℝ ∞ u (ball x₀ R) →
      ConstCoeffL2Bound a K (ball x₀ R) → ∀ p : ℕ,
        ENNReal.ofReal (1 / p !) * ballWeightedSeminorm (derivWordNorm (r + p) u) x₀ R (r + p) ≤
          ENNReal.ofReal K₃ * (ENNReal.ofReal (1 / p !) *
              ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p) +
            ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (1 / (p - q) !) *
              ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q)) := by
  set A := ∑ w, ‖a w‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun w _ => norm_nonneg _
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set S := ∑ q ∈ Finset.Icc 1 r, A * (r.choose q : ℝ) * ballCutoffConst q with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun q _ => by
    have := ballCutoffConst_nonneg q
    positivity
  set K₃ := Real.exp (r + 1) * K' * (1 + S) * ((r : ℝ) + 2) ^ r + 1 with hK₃
  have hbase : Real.exp (r + 1) * K' ≤ Real.exp (r + 1) * K' * (1 + S) * ((r : ℝ) + 2) ^ r := by
    have h1 : (1 : ℝ) ≤ (1 + S) * ((r : ℝ) + 2) ^ r :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
    have h0 : 0 ≤ Real.exp (r + 1) * K' := by positivity
    nlinarith
  refine ⟨K₃, by positivity, fun x₀ R u hu hP p => ?_⟩
  have h := ballWeightedSeminorm_add_le hK'0 hu (hP.of_le (le_max_left K 0)) p
  have hfac : (0 : ℝ) < p ! := by exact_mod_cast Nat.factorial_pos p
  calc ENNReal.ofReal (1 / p !) * ballWeightedSeminorm (derivWordNorm (r + p) u) x₀ R (r + p)
      ≤ ENNReal.ofReal (1 / p !) * (ENNReal.ofReal (Real.exp (r + 1) * K') *
          ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p) +
        ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (Real.exp (r + 1) * K' *
            (A * (r.choose q : ℝ) * ballCutoffConst q) * ((p : ℝ) + 2) ^ q) *
          ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q)) :=
        mul_le_mul' le_rfl h
    _ = ENNReal.ofReal (1 / p ! * (Real.exp (r + 1) * K')) *
          ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p) +
        ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (1 / p ! * (Real.exp (r + 1) * K' *
            (A * (r.choose q : ℝ) * ballCutoffConst q) * ((p : ℝ) + 2) ^ q)) *
          ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q) := by
        rw [mul_add, Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (K₃ * (1 / p !)) *
          ballWeightedSeminorm (derivWordNorm p (constCoeffAction a u)) x₀ R (r + p) +
        ∑ q ∈ Finset.Icc 1 r, ENNReal.ofReal (K₃ * (1 / (p - q) !)) *
          ballWeightedSeminorm (derivWordNorm (r + p - q) u) x₀ R (r + p - q) := by
        refine add_le_add ?_ (Finset.sum_le_sum fun q hq => ?_)
        · refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith
        · refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have hqr := (Finset.mem_Icc.1 hq).2
          have hfacq : (0 : ℝ) < (p - q) ! := by exact_mod_cast Nat.factorial_pos (p - q)
          have hCq : A * (r.choose q : ℝ) * ballCutoffConst q ≤ S :=
            Finset.single_le_sum (f := fun q => A * (r.choose q : ℝ) * ballCutoffConst q)
              (fun q _ => by have := ballCutoffConst_nonneg q; positivity) hq
          have hnat : (p + 2) ^ q * (p - q)! ≤ (r + 2) ^ r * p ! :=
            (pow_mul_factorial_sub_le p q).trans
              (Nat.mul_le_mul_right _ ((Nat.pow_le_pow_left (by omega) q).trans
                (Nat.pow_le_pow_right (by omega) hqr)))
          have hreal : ((p : ℝ) + 2) ^ q * (p - q)! ≤ ((r : ℝ) + 2) ^ r * p ! := by
            exact_mod_cast hnat
          have hratio : 1 / (p ! : ℝ) * ((p : ℝ) + 2) ^ q ≤ ((r : ℝ) + 2) ^ r * (1 / (p - q)!) := by
            rw [div_mul_eq_mul_div, one_mul, mul_one_div, div_le_div_iff₀ hfac hfacq]
            linarith
          have hpos : 0 ≤ Real.exp (r + 1) * K' * (A * (r.choose q : ℝ) * ballCutoffConst q) := by
            have := ballCutoffConst_nonneg q
            positivity
          calc 1 / (p ! : ℝ) * (Real.exp (r + 1) * K' *
                (A * (r.choose q : ℝ) * ballCutoffConst q) * ((p : ℝ) + 2) ^ q)
              = Real.exp (r + 1) * K' * (A * (r.choose q : ℝ) * ballCutoffConst q) *
                  (1 / (p ! : ℝ) * ((p : ℝ) + 2) ^ q) := by ring
            _ ≤ Real.exp (r + 1) * K' * (A * (r.choose q : ℝ) * ballCutoffConst q) *
                  (((r : ℝ) + 2) ^ r * (1 / (p - q)!)) :=
                mul_le_mul_of_nonneg_left hratio hpos
            _ ≤ Real.exp (r + 1) * K' * (1 + S) * (((r : ℝ) + 2) ^ r * (1 / (p - q)!)) := by
                gcongr
                linarith
            _ ≤ K₃ * (1 / (p - q)!) := by
                rw [hK₃]
                have : 0 ≤ 1 / ((p - q)! : ℝ) := by positivity
                nlinarith
    _ = _ := by
        rw [mul_add, Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end Weighted

end Langlands.Analysis
