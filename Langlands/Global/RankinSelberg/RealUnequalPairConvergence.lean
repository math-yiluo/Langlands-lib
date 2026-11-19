import Langlands.Global.RankinSelberg.RealUnequalDualConvergence
import Langlands.Global.RankinSelberg.RealEqualDualConvergence
import Langlands.Representation.Whittaker.DualTransform

/-! # Convergence and holomorphy of both real unequal-rank Rankin–Selberg integrals -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalPairConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence
  RealRectangularIwasawa RealUnequalDualConvergence

local instance realUPairGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realUPairGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realUPairNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realUPairNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realUPairQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance realUPairQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {r t : ℕ}

/-! ### Orthogonality of `w_(n,m)` -/

theorem weylLong_mem_unitary' (N : ℕ) :
    GeneralLinear.weylLong N ℝ ∈ unitaryCompact ℝ N := by
  show ((GeneralLinear.weylLong N ℝ : Langlands.GeneralLinear N ℝ) :
    Matrix (Fin N) (Fin N) ℝ) ∈ Matrix.unitaryGroup (Fin N) ℝ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  have h := congrArg Units.val (GeneralLinear.inverseTranspose_weylLong N ℝ)
  rw [GeneralLinear.inverseTranspose_coe, GeneralLinear.weylLong_inv] at h
  rw [h, ← Units.val_mul, GeneralLinear.weylLong_mul_self, Units.val_one]

theorem reindex_mem_unitary {a b : ℕ} (e : Fin a ≃ Fin b) {g : Langlands.GeneralLinear a ℝ}
    (hg : g ∈ unitaryCompact ℝ a) : GeneralLinear.reindex e g ∈ unitaryCompact ℝ b := by
  have hg' : ((g : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) ∈
      Matrix.unitaryGroup (Fin a) ℝ := hg
  rw [Matrix.mem_unitaryGroup_iff'] at hg'
  show ((GeneralLinear.reindex e g : Langlands.GeneralLinear b ℝ) :
    Matrix (Fin b) (Fin b) ℝ) ∈ Matrix.unitaryGroup (Fin b) ℝ
  rw [Matrix.mem_unitaryGroup_iff']
  change star (Matrix.reindex e e (g : Matrix (Fin a) (Fin a) ℝ)) *
    Matrix.reindex e e (g : Matrix (Fin a) (Fin a) ℝ) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex, ← Matrix.star_eq_conjTranspose,
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hg',
    Matrix.submatrix_one_equiv]

theorem blockSum_mem_unitary {a b : ℕ} {g : Langlands.GeneralLinear a ℝ}
    {k : Langlands.GeneralLinear b ℝ} (hg : g ∈ unitaryCompact ℝ a)
    (hk : k ∈ unitaryCompact ℝ b) : GeneralLinear.blockSum (g, k) ∈ unitaryCompact ℝ (a + b) := by
  have hg' : ((g : Langlands.GeneralLinear a ℝ) : Matrix (Fin a) (Fin a) ℝ) ∈
      Matrix.unitaryGroup (Fin a) ℝ := hg
  have hk' : ((k : Langlands.GeneralLinear b ℝ) : Matrix (Fin b) (Fin b) ℝ) ∈
      Matrix.unitaryGroup (Fin b) ℝ := hk
  rw [Matrix.mem_unitaryGroup_iff'] at hg' hk'
  show ((GeneralLinear.blockSum (g, k) : Langlands.GeneralLinear (a + b) ℝ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℝ) ∈ Matrix.unitaryGroup (Fin (a + b)) ℝ
  rw [Matrix.mem_unitaryGroup_iff']
  change star (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (g : Matrix (Fin a) (Fin a) ℝ) 0 0 (k : Matrix (Fin b) (Fin b) ℝ))) *
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (g : Matrix (Fin a) (Fin a) ℝ) 0 0 (k : Matrix (Fin b) (Fin b) ℝ)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose,
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  simp only [← Matrix.star_eq_conjTranspose, hg', hk', Matrix.conjTranspose_zero, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem unfoldingWeyl_mem_unitary (h : t < r) :
    (unfoldingWeyl h : Langlands.GeneralLinear (r + 1) ℝ) ∈ unitaryCompact ℝ (r + 1) :=
  reindex_mem_unitary _ (blockSum_mem_unitary (unitaryCompact ℝ (t + 1)).one_mem
    (weylLong_mem_unitary' _))

/-- Right translation by an orthogonal matrix preserves the gauge estimate. -/
theorem hasGauge_translate {n : ℕ} {F : Langlands.GeneralLinear (n + 1) ℝ → ℂ} (hF : HasGauge F)
    {k₀ : Langlands.GeneralLinear (n + 1) ℝ} (hk₀ : k₀ ∈ unitaryCompact ℝ (n + 1)) :
    HasGauge (translateFunction k₀ F) := by
  obtain ⟨N, hN⟩ := hF
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun y k => ?_⟩
  have := hb y ⟨(k : Langlands.GeneralLinear (n + 1) ℝ) * k₀,
    (unitaryCompact ℝ (n + 1)).mul_mem k.2 hk₀⟩
  unfold translateFunction
  rwa [mul_assoc]

/-! ### The Whittaker character on reflected and padded unipotent matrices -/

theorem realWhittakerCharacter_reflected {n : ℕ} (a : ℝˣ)
    (u : Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) :
    realWhittakerCharacter a (Langlands.Whittaker.reflectedUnipotent u).val =
      realWhittakerCharacter (-a) u.val := by
  have hs := Langlands.Whittaker.reflectedUnipotent_sum u
  unfold realWhittakerCharacter
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    LocalFactor.Archimedean.realScaledCharacter_apply, Real.fourierChar_apply, Units.val_neg]
  rw [hs]
  push_cast
  ring_nf

theorem norm_realWhittakerCharacter {n : ℕ} (a : ℝˣ) (u : Langlands.GeneralLinear (n + 1) ℝ) :
    ‖realWhittakerCharacter a u‖ = 1 := by
  unfold realWhittakerCharacter
  exact HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex _ _

/-! ### Block multiplication and the padded unipotent matrix -/

open Langlands.GeneralLinear (lowerBlockFirst lowerBlockMiddle lowerBlockLast) in
theorem index_cases {a d : ℕ} (i : Fin (a + d + 1)) :
    (∃ j, i = lowerBlockFirst d 1 j) ∨ (∃ l, i = lowerBlockMiddle a 1 l) ∨
      i = lowerBlockLast a d 0 := by
  induction i using Fin.addCases with
  | left i' =>
    induction i' using Fin.addCases with
    | left j => exact Or.inl ⟨j, rfl⟩
    | right l => exact Or.inr (Or.inl ⟨l, rfl⟩)
  | right i' =>
    refine Or.inr (Or.inr ?_)
    rw [Subsingleton.elim i' 0]
    rfl

open Langlands.GeneralLinear (lowerBlockFirst lowerBlockMiddle lowerBlockLast) in
theorem rect_mul {a d : ℕ} (u g : Langlands.GeneralLinear a ℝ) (x : Matrix (Fin d) (Fin a) ℝ) :
    rect (u * g) x = rect u 0 * rect g x := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rcases index_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;>
  rcases index_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl <;>
  simp [Matrix.mul_apply, sum_split, Matrix.one_apply]

open Langlands.GeneralLinear (lowerBlockFirst lowerBlockMiddle lowerBlockLast) in
theorem rect_zero_apply {a d : ℕ} (u : Langlands.GeneralLinear a ℝ) (i j : Fin (a + d + 1)) :
    ((rect u (0 : Matrix (Fin d) (Fin a) ℝ) : Langlands.GeneralLinear (a + d + 1) ℝ) :
      Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) i j =
      if hij : (i : ℕ) < a ∧ (j : ℕ) < a then
        (u : Matrix (Fin a) (Fin a) ℝ) ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin (a + d + 1)) (Fin (a + d + 1)) ℝ) i j := by
  have vF : ∀ k : Fin a, ((lowerBlockFirst d 1 k : Fin (a + d + 1)) : ℕ) = k := fun _ => rfl
  have vM : ∀ k : Fin d, ((lowerBlockMiddle a 1 k : Fin (a + d + 1)) : ℕ) = a + k :=
    fun _ => rfl
  have vL : ((lowerBlockLast a d 0 : Fin (a + d + 1)) : ℕ) = a + d := rfl
  rcases index_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;>
  rcases index_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl <;>
  simp only [Langlands.GeneralLinear.lowerBlockLocalization_11,
    Langlands.GeneralLinear.lowerBlockLocalization_12,
    Langlands.GeneralLinear.lowerBlockLocalization_13,
    Langlands.GeneralLinear.lowerBlockLocalization_21,
    Langlands.GeneralLinear.lowerBlockLocalization_22,
    Langlands.GeneralLinear.lowerBlockLocalization_23,
    Langlands.GeneralLinear.lowerBlockLocalization_31,
    Langlands.GeneralLinear.lowerBlockLocalization_32,
    Langlands.GeneralLinear.lowerBlockLocalization_33] <;>
  simp [vF, vM, vL, Matrix.one_apply, Fin.ext_iff] <;>
  omega

theorem rectangularPoint_mul (h : t < r) (u g : Langlands.GeneralLinear (t + 1) ℝ)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :
    rectangularPoint h (u * g) x = rectangularPoint h u 0 * rectangularPoint h g x := by
  rw [rectangularPoint_eq, rectangularPoint_eq, rectangularPoint_eq, rect_mul, map_mul]

theorem rectangularPoint_zero (h : t < r) (u : Langlands.GeneralLinear (t + 1) ℝ) :
    rectangularPoint h u 0 = padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) u := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [UnequalAnalytic.padGL_apply, rectangularPoint_eq]
  change ((rect u (0 : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :
      Langlands.GeneralLinear (t + 1 + (r - (t + 1)) + 1) ℝ) :
    Matrix (Fin (t + 1 + (r - (t + 1)) + 1)) (Fin (t + 1 + (r - (t + 1)) + 1)) ℝ)
      (Fin.cast (rect_size h).symm i) (Fin.cast (rect_size h).symm j) = _
  rw [rect_zero_apply]
  simp only [Fin.val_cast]
  split_ifs with hij
  · rfl
  · simp [Matrix.one_apply, Fin.ext_iff]

/-! ### Convergence of both integrals for uniformly regular functions -/

section Regular

open RealLocalWhittaker (iteratedRightDerivative regularFunctions)
open RealEqualDualConvergence (hasGauge_dual continuous_dual)

set_option backward.isDefEq.respectTransparency false in
/-- **Convergence and holomorphy of both unequal-rank integrals for uniformly regular
functions.** -/
theorem exists_pair_convergence_of_regular (h : t < r) (D : RealQuotientMeasureData t) {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hreg : ∀ Xs, iteratedRightDerivative r Xs W ∈ regularFunctions r a)
    (hgrowth : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N)
    (hreg' : ∀ Xs, iteratedRightDerivative t Xs W' ∈ regularFunctions t (-a))
    (hgrowth' : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative t Xs W' g‖ ≤ C * realMatrixHeight g ^ N) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure) ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (realUnequalDualKernel h W W' s) (realUnequalDualMeasure (r := r) a D)) ∧
      DifferentiableOn ℂ (realUnequalIntegral h D W W') {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realUnequalDualIntegral h a D W W') {s : ℂ | σ < s.re} := by
  obtain ⟨σ1, h1, h3⟩ :=
    RealUnequalConvergence.exists_convergence_of_regular h D hreg hgrowth hreg' hgrowth'
  have hW : W ∈ regularFunctions r a := hreg []
  have hW' : W' ∈ regularFunctions t (-a) := hreg' []
  have hgW := RealWhittakerGauge.exists_gauge_bound hreg hgrowth
  have hgW' := RealWhittakerGauge.exists_gauge_bound hreg' hgrowth'
  set hp : t + 1 ≤ r + 1 := Nat.le_of_lt (Nat.succ_lt_succ h) with hhp
  set V := translateFunction (unfoldingWeyl h) (ArchimedeanLocal.dualFunction (r + 1) W) with hVdef
  set V' := ArchimedeanLocal.dualFunction (t + 1) W' with hV'def
  have hVc : Continuous V :=
    (continuous_dual hW.2.1.continuous).comp (continuous_id.mul continuous_const)
  have hV'c : Continuous V' := continuous_dual hW'.2.1.continuous
  -- the left character of `V`
  have hVchar : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      V (u * g) = realWhittakerCharacter (-a) u * V g := by
    intro u hu g
    show W (GeneralLinear.weylInverseTranspose (r + 1) ℝ (u * g * unfoldingWeyl h)) =
      realWhittakerCharacter (-a) u *
        W (GeneralLinear.weylInverseTranspose (r + 1) ℝ (g * unfoldingWeyl h))
    rw [mul_assoc, show u * (g * unfoldingWeyl h) =
      (⟨u, hu⟩ : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ).val * (g * unfoldingWeyl h)
        from rfl, Langlands.Whittaker.weylInverseTranspose_left_unipotent,
      hW.1 _ (Langlands.Whittaker.reflectedUnipotent ⟨u, hu⟩).2,
      realWhittakerCharacter_reflected]
  have hV'char : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g,
      V' (u * g) = realWhittakerCharacter a u * V' g := by
    intro u hu g
    show W' (GeneralLinear.weylInverseTranspose (t + 1) ℝ (u * g)) =
      realWhittakerCharacter a u * W' (GeneralLinear.weylInverseTranspose (t + 1) ℝ g)
    rw [show u * g = (⟨u, hu⟩ : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ).val * g
        from rfl, Langlands.Whittaker.weylInverseTranspose_left_unipotent,
      hW'.1 _ (Langlands.Whittaker.reflectedUnipotent ⟨u, hu⟩).2,
      realWhittakerCharacter_reflected, neg_neg]
  have hVabs : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      ‖V (u * g)‖ = ‖V g‖ := by
    intro u hu g
    rw [hVchar u hu g, norm_mul, norm_realWhittakerCharacter, one_mul]
  have hgV : HasGauge V :=
    hasGauge_translate (hasGauge_dual hgW) (unfoldingWeyl_mem_unitary h)
  have hgV' : HasGauge V' := hasGauge_dual hgW'
  have hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g x,
      bkernel h V V' (u * g, x) = bkernel h V V' (g, x) := by
    intro u hu g x
    unfold bkernel
    simp only
    rw [rectangularPoint_mul, rectangularPoint_zero,
      hVchar _ (RealUnequalConvergence.padGL_mem_upperUnipotent _ hu),
      RealUnequalConvergence.realWhittakerCharacter_padGL h, hV'char u hu g]
    calc
      realWhittakerCharacter (-a) u * V (rectangularPoint h g x) *
          (realWhittakerCharacter a u * V' g) =
          (realWhittakerCharacter (-a) u * realWhittakerCharacter (-(-a)) u) *
            (V (rectangularPoint h g x) * V' g) := by
        rw [neg_neg]
        ring
      _ = V (rectangularPoint h g x) * V' g := by
        rw [realWhittakerCharacter_mul_neg, one_mul]
  obtain ⟨σ2, h2, h4⟩ := exists_dual_convergence h D (realSelfDualMeasure a) hVc hV'c hVabs hinv
    hgV hgV'
  refine ⟨max σ1 σ2, fun s hs => h1 s (lt_of_le_of_lt (le_max_left _ _) hs),
    fun s hs => h2 s (lt_of_le_of_lt (le_max_right _ _) hs),
    h3.mono fun s (hs : max σ1 σ2 < s.re) =>
      (show σ1 < s.re from lt_of_le_of_lt (le_max_left _ _) hs),
    h4.mono fun s (hs : max σ1 σ2 < s.re) =>
      (show σ2 < s.re from lt_of_le_of_lt (le_max_right _ _) hs)⟩

end Regular

end Langlands.Global.RankinSelbergGlobal.RealUnequalPairConvergence

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

local instance realUPairStatementGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realUPairStatementGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realUPairStatementNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realUPairStatementNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realUPairStatementQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realUPairStatementQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- **Convergence and holomorphy of both real unequal-rank Rankin–Selberg integrals**
(Jacquet 2009, Theorem 2.1(i) for the two integrals of the unequal-rank functional equation
(ii), real case, with holomorphy in the region of convergence). Let `t < r`, let `W` on
`GL_(r+1)(ℝ)` and `W'` on `GL_(t+1)(ℝ)` be functions all of whose iterated right derivatives are
smooth, transform on the left under the upper unipotent group by the characters for `a` and `-a`
respectively, and are bounded by a constant times a fixed power (independent of the derivative)
of the matrix height. Then there is `σ` such that for `Re s > σ` the integrand of `Ψ(s; W, W')`
is integrable for the quotient measure of `D`, the kernel of the dual block integral
`Ψ_(n-m-1)(s; ρ(w_(n,m)) W̃, W̃')` is integrable for the product of that quotient measure and the
rectangular measure self-dual for `realScaledCharacter a`, and both integrals are holomorphic on
`Re s > σ`. These are the first four conjuncts of `RealJacquet.UnequalEquation h a D W W' …`. -/
def RealUnequalPairConvergenceStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t) (a : ℝˣ)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W ∈
      RealLocalWhittaker.regularFunctions r a) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N) →
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W' ∈
      RealLocalWhittaker.regularFunctions t (-a)) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative t Xs W' g‖ ≤ C * realMatrixHeight g ^ N) →
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure) ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (realUnequalDualKernel h W W' s) (realUnequalDualMeasure (r := r) a D)) ∧
      DifferentiableOn ℂ (realUnequalIntegral h D W W') {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realUnequalDualIntegral h a D W W') {s : ℂ | σ < s.re}

theorem realUnequalPairConvergence : RealUnequalPairConvergenceStatement :=
  fun _ _ h D _ _ _ hreg hgrowth hreg' hgrowth' =>
    RealUnequalPairConvergence.exists_pair_convergence_of_regular h D hreg hgrowth hreg' hgrowth'

end Langlands.Global.RankinSelbergGlobal
