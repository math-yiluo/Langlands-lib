import Langlands.Representation.Archimedean.RealTaylorLeftPolynomial
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Proof of `RealTaylorLeftPolynomialStatement`
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator Topology Nat

open Filter Asymptotics Polynomial

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

namespace RealTaylorLeftPolynomialProof

/-! ## One-variable calculus -/

/-- A complex polynomial of degree `≤ k` that is `o(t^k)` at `0` (on the punctured
neighbourhood) vanishes. -/
theorem eq_zero_of_isLittleO_pow {k : ℕ} {q : Polynomial ℂ} (hq : q.natDegree ≤ k)
    (h : (fun t : ℝ => q.eval (t : ℂ)) =o[𝓝[≠] (0 : ℝ)] fun t => t ^ k) : q = 0 := by
  induction k generalizing q with
  | zero =>
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp (Nat.le_zero.mp hq)
    simp only [eval_C, pow_zero] at h
    have ht : Tendsto (fun _ : ℝ => a) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      (isLittleO_one_iff (F := ℝ)).mp h
    rw [tendsto_const_nhds_iff] at ht
    rw [ht, C_0]
  | succ k ih =>
    have h0 : q.eval 0 = 0 := by
      have ht1 : Tendsto (fun t : ℝ => q.eval (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
        h.trans_tendsto (by
          have hc : Continuous fun t : ℝ => t ^ (k + 1) := continuous_pow _
          simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds)
      have ht2 : Tendsto (fun t : ℝ => q.eval (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 (q.eval 0)) := by
        have hc : Continuous fun t : ℝ => q.eval (t : ℂ) :=
          q.continuous.comp Complex.continuous_ofReal
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique ht2 ht1
    have hdvd : X ∣ q := by
      rw [X_dvd_iff, coeff_zero_eq_eval_zero, h0]
    obtain ⟨q', rfl⟩ := hdvd
    by_cases hq0 : q' = 0
    · rw [hq0, mul_zero]
    have hq' : q'.natDegree ≤ k := by
      rw [natDegree_X_mul hq0] at hq
      omega
    have h' : (fun t : ℝ => q'.eval (t : ℂ)) =o[𝓝[≠] (0 : ℝ)] fun t => t ^ k := by
      rw [isLittleO_iff]
      intro c hc
      filter_upwards [isLittleO_iff.mp h hc, self_mem_nhdsWithin] with t ht htne
      have htne' : t ≠ 0 := htne
      have hpos : 0 < ‖t‖ := norm_pos_iff.mpr htne'
      simp only [eval_mul, eval_X, norm_mul, Complex.norm_real, pow_succ] at ht
      rw [mul_comm ‖t ^ k‖ ‖t‖, ← mul_assoc, mul_comm c ‖t‖, mul_assoc] at ht
      exact le_of_mul_le_mul_left ht hpos
    rw [ih hq' h', mul_zero]

/-- The coefficients of the Taylor polynomial of order `k` at `0`. -/
def taylorPoly (f : ℝ → ℂ) (s : Set ℝ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k + 1), monomial j (((j ! : ℝ)⁻¹ : ℂ) * iteratedDerivWithin j f s 0)

theorem taylorPoly_natDegree_le (f : ℝ → ℂ) (s : Set ℝ) (k : ℕ) :
    (taylorPoly f s k).natDegree ≤ k :=
  natDegree_sum_le_of_forall_le _ _ fun _ hj =>
    (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem taylorPoly_coeff (f : ℝ → ℂ) (s : Set ℝ) (k : ℕ) :
    (taylorPoly f s k).coeff k = ((k ! : ℝ)⁻¹ : ℂ) * iteratedDerivWithin k f s 0 := by
  rw [taylorPoly, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (k + 1)) k]
  simp

theorem taylorPoly_eval (f : ℝ → ℂ) (s : Set ℝ) (k : ℕ) (x : ℝ) :
    (taylorPoly f s k).eval (x : ℂ) = taylorWithinEval f k s 0 x := by
  rw [taylor_within_apply, taylorPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_monomial, sub_zero, Complex.real_smul]
  push_cast
  ring

/-- If `f` is `C^k` on an open convex neighbourhood of `0` and `f - q = o(t^k)` for a
polynomial `q` of degree `≤ k`, then `f^{(k)}(0) = k! · q_k`. -/
theorem iteratedDeriv_eq_of_isLittleO {k : ℕ} {f : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s)
    (hsc : Convex ℝ s) (h0 : (0 : ℝ) ∈ s) (hf : ContDiffOn ℝ k f s) {q : Polynomial ℂ}
    (hq : q.natDegree ≤ k)
    (h : (fun t : ℝ => f t - q.eval (t : ℂ)) =o[𝓝 (0 : ℝ)] fun t => t ^ k) :
    iteratedDeriv k f 0 = (k ! : ℂ) * q.coeff k := by
  have ht := taylor_isLittleO hsc h0 hf
  rw [hs.nhdsWithin_eq h0] at ht
  simp only [sub_zero] at ht
  have hdiff : (fun t : ℝ => (taylorPoly f s k - q).eval (t : ℂ)) =o[𝓝 (0 : ℝ)]
      fun t => t ^ k := by
    have := h.sub ht
    refine this.congr_left fun t => ?_
    rw [eval_sub, taylorPoly_eval]
    ring
  have hz := eq_zero_of_isLittleO_pow
    ((natDegree_sub_le _ _).trans (max_le (taylorPoly_natDegree_le f s k) hq))
    (hdiff.mono nhdsWithin_le_nhds)
  have hc := congrArg (fun r => r.coeff k) (sub_eq_zero.mp hz)
  simp only [taylorPoly_coeff] at hc
  rw [← iteratedDerivWithin_of_isOpen hs h0, ← hc]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  push_cast
  field_simp

/-- The polynomial `∑_{j ≤ k} c_j X^j (1 + x X)^(k - 1 - j)` (natural subtraction, so the
term `j = k` is `c_k X^k`). -/
def bolPoly (c : ℕ → ℂ) (x : ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (k + 1), C (c j) * X ^ j * (1 + C x * X) ^ (k - 1 - j)

theorem bolTerm_natDegree_le (c : ℂ) (x : ℂ) (j m : ℕ) :
    (C c * X ^ j * (1 + C x * X) ^ m).natDegree ≤ j + m := by
  have h1 : (1 + C x * X).natDegree ≤ 1 := by compute_degree
  refine natDegree_mul_le.trans (add_le_add (natDegree_C_mul_X_pow_le c j) ?_)
  exact natDegree_pow_le.trans (by nlinarith)

theorem bolPoly_natDegree_le (c : ℕ → ℂ) (x : ℂ) (k : ℕ) :
    (bolPoly c x k).natDegree ≤ k :=
  natDegree_sum_le_of_forall_le _ _ fun j hj => by
    have hj' := Finset.mem_range.mp hj
    exact (bolTerm_natDegree_le _ _ _ _).trans (by omega)

theorem bolPoly_coeff (c : ℕ → ℂ) (x : ℂ) (k : ℕ) :
    (bolPoly c x k).coeff k = c k := by
  rw [bolPoly, finsetSum_coeff, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · rw [show k - 1 - k = 0 by omega, pow_zero, mul_one, coeff_C_mul_X_pow]
    simp
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact coeff_eq_zero_of_natDegree_lt ((bolTerm_natDegree_le _ _ _ _).trans_lt (by omega))

/-- The algebraic identity behind the Bol identity: for `y = 1 + t x ≠ 0`,
`y^(k-1) T(t / y) - W(t) = c_k t^k (y⁻¹ - 1)`. -/
theorem bolPoly_identity (c : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k) (t x : ℂ) (hy : 1 + t * x ≠ 0) :
    (1 + t * x) ^ (k - 1) * (∑ j ∈ Finset.range (k + 1), monomial j (c j)).eval (t / (1 + t * x))
        - (bolPoly c x k).eval t =
      c k * t ^ k * ((1 + t * x)⁻¹ - 1) := by
  rw [bolPoly, eval_finsetSum, eval_finsetSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · simp only [eval_monomial, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
    rw [show k - 1 - k = 0 by omega, pow_zero, mul_one, div_pow]
    have hpow : (1 + t * x) ^ k = (1 + t * x) ^ (k - 1) * (1 + t * x) := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [hpow]
    have hy' : (1 + t * x) ^ (k - 1) ≠ 0 := pow_ne_zero _ hy
    field_simp
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [eval_monomial, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
    rw [div_pow, mul_comm x t]
    have hpow : (1 + t * x) ^ (k - 1) = (1 + t * x) ^ (k - 1 - j) * (1 + t * x) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hpow]
    have hyj : (1 + t * x) ^ j ≠ 0 := pow_ne_zero _ hy
    field_simp
    ring

/-- **Bol's identity at `0`.** For `ψ` of class `C^k` (`k ≥ 1`) and real `x`, the `k`-th
derivative at `0` of `t ↦ (1 + t x)^(k-1) ψ(t / (1 + t x))` is `ψ^{(k)}(0)`. -/
theorem iteratedDeriv_bol {k : ℕ} (hk : 1 ≤ k) {ψ : ℝ → ℂ} (hψ : ContDiff ℝ k ψ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (((1 + t * x) ^ (k - 1) : ℝ) : ℂ) * ψ (t / (1 + t * x))) 0 =
      iteratedDeriv k ψ 0 := by
  set c : ℕ → ℂ := fun j => ((j ! : ℝ)⁻¹ : ℂ) * iteratedDerivWithin j ψ Set.univ 0 with hc
  set T : Polynomial ℂ := taylorPoly ψ Set.univ k with hT
  have hTsum : T = ∑ j ∈ Finset.range (k + 1), monomial j (c j) := rfl
  set W : Polynomial ℂ := bolPoly c (x : ℂ) k with hW
  set δ : ℝ := 1 / (2 * (|x| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set s : Set ℝ := Set.Ioo (-δ) δ with hs
  have hsy : ∀ t ∈ s, 0 < 1 + t * x := by
    intro t ht
    have h1 : |t| < δ := abs_lt.mpr ht
    have h2 : |t * x| ≤ |t| * (|x| + 1) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
    have h3 : |t| * (|x| + 1) < 1 / 2 := by
      calc |t| * (|x| + 1) < δ * (|x| + 1) :=
            mul_lt_mul_of_pos_right h1 (by positivity)
        _ = 1 / 2 := by rw [hδ]; field_simp
    have := neg_abs_le (t * x)
    linarith
  have h0s : (0 : ℝ) ∈ s := ⟨by linarith, hδpos⟩
  have hsnhds : s ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds h0s
  -- Taylor's theorem for `ψ`.
  have hTay : (fun u : ℝ => ψ u - T.eval (u : ℂ)) =o[𝓝 (0 : ℝ)] fun u => u ^ k := by
    have := taylor_isLittleO_univ (x₀ := 0) hψ
    simp only [sub_zero] at this
    refine this.congr_left fun u => ?_
    rw [hT, taylorPoly_eval]
  -- The substitution `σ(t) = t / (1 + t x)`.
  have hσc : ContinuousAt (fun t : ℝ => t / (1 + t * x)) 0 :=
    continuousAt_id.div (continuousAt_const.add (continuousAt_id.mul continuousAt_const))
      (by simp)
  have hσ : Tendsto (fun t : ℝ => t / (1 + t * x)) (𝓝 0) (𝓝 0) := by
    simpa using hσc.tendsto
  have hinv : Tendsto (fun t : ℝ => (1 + t * x)⁻¹) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => (1 + t * x)⁻¹) 0 :=
      (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).inv₀ (by simp)
    simpa using hc.tendsto
  have hσO : (fun t : ℝ => t / (1 + t * x)) =O[𝓝 0] fun t => t := by
    have h := (isBigO_refl (fun t : ℝ => t) (𝓝 0)).mul (hinv.isBigO_one (F := ℝ))
    simpa [div_eq_mul_inv] using h
  have hcomp : (fun t : ℝ => ψ (t / (1 + t * x)) - T.eval ((t / (1 + t * x) : ℝ) : ℂ)) =o[𝓝 0]
      fun t => t ^ k :=
    (hTay.comp_tendsto hσ).trans_isBigO (hσO.pow k)
  have hfac : (fun t : ℝ => (((1 + t * x) ^ (k - 1) : ℝ) : ℂ)) =O[𝓝 0] fun _ => (1 : ℝ) := by
    have hc : ContinuousAt (fun t : ℝ => (((1 + t * x) ^ (k - 1) : ℝ) : ℂ)) 0 :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _)
    exact hc.tendsto.isBigO_one (F := ℝ)
  have hA := hfac.mul_isLittleO hcomp
  have hB : (fun t : ℝ => c k * (t : ℂ) ^ k * ((1 + (t : ℂ) * (x : ℂ))⁻¹ - 1)) =o[𝓝 0]
      fun t => t ^ k * 1 := by
    have h0 : (fun t : ℝ => (t : ℂ) ^ k) =O[𝓝 0] fun t => t ^ k :=
      isBigO_of_le _ fun t => by simp
    have h1 : (fun t : ℝ => c k * (t : ℂ) ^ k) =O[𝓝 0] fun t => t ^ k :=
      h0.const_mul_left (c k)
    have h2 : (fun t : ℝ => (1 + (t : ℂ) * (x : ℂ))⁻¹ - 1) =o[𝓝 0] fun _ => (1 : ℝ) := by
      refine (isLittleO_one_iff (F := ℝ)).mpr ?_
      have hc : ContinuousAt (fun t : ℝ => (1 + (t : ℂ) * (x : ℂ))⁻¹ - 1) 0 :=
        ((continuousAt_const.add ((Complex.continuous_ofReal.continuousAt).mul
          continuousAt_const)).inv₀ (by simp)).sub continuousAt_const
      simpa using hc.tendsto
    exact h1.mul_isLittleO h2
  have hmain : (fun t : ℝ => (((1 + t * x) ^ (k - 1) : ℝ) : ℂ) * ψ (t / (1 + t * x)) -
      W.eval (t : ℂ)) =o[𝓝 0] fun t => t ^ k := by
    simp only [one_mul] at hA
    simp only [mul_one] at hB
    have hsum := hA.add hB
    refine hsum.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hsnhds] with t ht
    have hy : (1 : ℂ) + (t : ℂ) * (x : ℂ) ≠ 0 := by
      have := hsy t ht
      exact_mod_cast this.ne'
    have hid := bolPoly_identity c hk (t : ℂ) (x : ℂ) hy
    rw [← hTsum] at hid
    rw [hW, ← hid]
    push_cast
    ring
  have hcd : ContDiffOn ℝ k
      (fun t : ℝ => (((1 + t * x) ^ (k - 1) : ℝ) : ℂ) * ψ (t / (1 + t * x))) s := by
    have h1 : ContDiff ℝ k (fun t : ℝ => (((1 + t * x) ^ (k - 1) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((contDiff_const.add (contDiff_id.mul contDiff_const)).pow _)
    have h2 : ContDiffOn ℝ k (fun t : ℝ => ψ (t / (1 + t * x))) s :=
      hψ.comp_contDiffOn (contDiffOn_id.div (contDiffOn_const.add
        (contDiffOn_id.mul contDiffOn_const)) fun t ht => (hsy t ht).ne')
    exact h1.contDiffOn.mul h2
  rw [iteratedDeriv_eq_of_isLittleO isOpen_Ioo (convex_Ioo _ _) h0s hcd
    (bolPoly_natDegree_le c _ k) hmain, bolPoly_coeff c _ k, hc]
  simp only [iteratedDerivWithin_univ]
  have hk' : ((k ! : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  push_cast at hk' ⊢
  field_simp

/-- A smooth function whose `k`-th derivative vanishes identically is a polynomial of degree
`< k` (Taylor's theorem with integral remainder). -/
theorem exists_poly_of_iteratedDeriv_eq_zero {k : ℕ} {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : ∀ t, iteratedDeriv k f t = 0) :
    ∃ q : Polynomial ℂ, q.degree < k ∧ ∀ t : ℝ, f t = q.eval (t : ℂ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, by simp, fun t => ?_⟩
    simpa using h t
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine ⟨∑ j ∈ Finset.range (n + 1), monomial j (((j ! : ℝ)⁻¹ : ℂ) * iteratedDeriv j f 0),
    ?_, ?_⟩
  · have hnat : (∑ j ∈ Finset.range (n + 1),
        monomial j (((j ! : ℝ)⁻¹ : ℂ) * iteratedDeriv j f 0)).natDegree ≤ n :=
      natDegree_sum_le_of_forall_le _ _ fun _ hj =>
        (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    exact (degree_le_of_natDegree_le hnat).trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  · intro t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [eval_finsetSum, Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [eval_monomial, zero_pow hj]
      · intro h0
        simp at h0
    · have hU : UniqueDiffOn ℝ (Set.uIcc 0 t) := uniqueDiffOn_uIcc (Ne.symm ht)
      have hrem := taylor_integral_remainder (x₀ := 0) (x := t) (n := n)
        (contDiff_infty.mp hf (n + 1)).contDiffOn
      have hint : ∫ s in (0 : ℝ)..t,
          ((t - s) ^ n / n !) • iteratedDerivWithin (n + 1) f (Set.uIcc 0 t) s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
        · simp
        · intro s hs
          simp only
          rw [iteratedDerivWithin_eq_iteratedDeriv hU
            (contDiff_infty.mp hf (n + 1)).contDiffAt hs, h s, smul_zero]
      rw [hint, sub_eq_zero, taylor_within_apply] at hrem
      rw [hrem, eval_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [iteratedDerivWithin_eq_iteratedDeriv hU (contDiff_infty.mp hf j).contDiffAt
        Set.left_mem_uIcc, eval_monomial, sub_zero, Complex.real_smul]
      push_cast
      ring

/-! ## Derivatives along the lower root group -/

section LowerRoot

variable {n p : ℕ} (hp : p + 1 < n)

/-- `s ↦ F(e(s))` has derivative `(R(E) F)(e(t))` at `t`. -/
theorem hasDerivAt_lowerRoot {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F) (t : ℝ) :
    HasDerivAt (fun s => F (lowerRootElement n p hp s))
      (rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp) F
        (lowerRootElement n p hp t)) t := by
  have hfun : (fun s => F (lowerRootElement n p hp s)) =
      fun s => unitsExtension F (1 + s • lowerRootMatrix n p hp) := by
    funext s
    rw [← lowerRootElement_val, unitsExtension_val]
  rw [hfun, rightDerivative_eq_fderiv hF, lowerRootElement_val, add_mul, one_mul,
    smul_mul_assoc, lowerRootMatrix_mul_self, smul_zero, add_zero]
  have hd : HasDerivAt (fun s : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + s • lowerRootMatrix n p hp)
      (lowerRootMatrix n p hp) t := by
    simpa using ((hasDerivAt_id t).smul_const (lowerRootMatrix n p hp)).const_add 1
  have hu : IsUnit (1 + t • lowerRootMatrix n p hp) := by
    rw [← lowerRootElement_val]
    exact Units.isUnit _
  exact (differentiableAt_unitsExtension hF hu).hasFDerivAt.comp_hasDerivAt t hd

/-- The iterated derivatives of `s ↦ F(e(s))` are the iterated right derivatives along `E`. -/
theorem iteratedDeriv_lowerRoot {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F) (m : ℕ) :
    iteratedDeriv m (fun s => F (lowerRootElement n p hp s)) =
      fun t => ((rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp))^[m] F)
        (lowerRootElement n p hp t) := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hd : deriv (fun s => F (lowerRootElement n p hp s)) =
        fun t => rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp) F
          (lowerRootElement n p hp t) :=
      funext fun t => (hasDerivAt_lowerRoot hp hF t).deriv
    rw [hd]
    exact ih (contMDiff_rightDerivative hF _)

/-- `s ↦ F(e(s))` is smooth. -/
theorem contDiff_lowerRoot {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F) :
    ContDiff ℝ ∞ (fun s => F (lowerRootElement n p hp s)) := by
  have hfun : (fun s => F (lowerRootElement n p hp s)) =
      unitsExtension F ∘ fun s => 1 + s • lowerRootMatrix n p hp := by
    funext s
    rw [Function.comp_apply, ← lowerRootElement_val, unitsExtension_val]
  rw [hfun]
  refine (contDiffOn_unitsExtension hF).comp_contDiff
    (contDiff_const.add (contDiff_id.smul contDiff_const)) fun s => ?_
  change IsUnit _
  rw [← lowerRootElement_val]
  exact Units.isUnit _

/-- The orbit function `t ↦ h(e(t) g)`. -/
def orbitFun (h : Langlands.GeneralLinear n ℝ → ℂ) (g : Langlands.GeneralLinear n ℝ) :
    ℝ → ℂ :=
  fun t => h (lowerRootElement n p hp t * g)

theorem contDiff_orbitFun {h : Langlands.GeneralLinear n ℝ → ℂ}
    (hh : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ h) (g : Langlands.GeneralLinear n ℝ) :
    ContDiff ℝ ∞ (orbitFun hp h g) :=
  contDiff_lowerRoot hp (F := fun x => h (x * g)) (hh.comp contMDiff_mul_right)

/-- Shifting along the orbit: `(d/dt)^m h(e(t) g)` at `t` is the derivative at `0` for the
point `e(t) g`. -/
theorem iteratedDeriv_orbitFun_shift (h : Langlands.GeneralLinear n ℝ → ℂ)
    (g : Langlands.GeneralLinear n ℝ) (m : ℕ) (t : ℝ) :
    iteratedDeriv m (orbitFun hp h g) t =
      iteratedDeriv m (orbitFun hp h (lowerRootElement n p hp t * g)) 0 := by
  have hfun : orbitFun hp h (lowerRootElement n p hp t * g) =
      fun s => orbitFun hp h g (s + t) := by
    funext s
    simp only [orbitFun]
    rw [← mul_assoc, lowerRootElement_add]
  rw [hfun, iteratedDeriv_comp_add_const]
  simp only [zero_add]

/-- The Taylor hypothesis of the statement in terms of the orbit function. -/
theorem iterate_rightDerivative_rightTranslation {h : Langlands.GeneralLinear n ℝ → ℂ}
    (hh : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ h) (g : Langlands.GeneralLinear n ℝ)
    (m : ℕ) :
    (rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp))^[m]
        (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) g h) 1 =
      iteratedDeriv m (orbitFun hp h g) 0 := by
  have h1 := congrFun (iteratedDeriv_lowerRoot hp (F := fun x => h (x * g))
    (hh.comp contMDiff_mul_right) m) 0
  have he : lowerRootElement n p hp 0 = 1 := by
    apply Units.ext
    simp
  rw [he] at h1
  exact h1.symm

end LowerRoot

/-! ## Matrix identities in `GL_n(ℝ)` -/

section Matrices

open Langlands.GeneralLinear

variable {n p : ℕ} (hp : p + 1 < n)

/-- The position `p`. -/
def idxP : Fin n := ⟨p, Nat.lt_of_succ_lt hp⟩

/-- The position `p + 1`. -/
def idxQ : Fin n := ⟨p + 1, hp⟩

theorem idxP_ne_idxQ : idxP hp ≠ idxQ hp := by
  simp [idxP, idxQ, Fin.ext_iff]

theorem idxQ_ne_idxP : idxQ hp ≠ idxP hp := (idxP_ne_idxQ hp).symm

theorem lowerRootMatrix_eq : lowerRootMatrix n p hp = Matrix.single (idxQ hp) (idxP hp) 1 :=
  rfl

/-- The matrix unit `E_{p,p+1}`. -/
def upperRootMatrix : Matrix (Fin n) (Fin n) ℝ := Matrix.single (idxP hp) (idxQ hp) 1

theorem upperRootMatrix_mul_self : upperRootMatrix hp * upperRootMatrix hp = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ (idxQ_ne_idxP hp) _

/-- The upper unipotent element `1 + x E_{p,p+1}`. -/
def upperRootElement (x : ℝ) : Langlands.GeneralLinear n ℝ where
  val := 1 + x • upperRootMatrix hp
  inv := 1 - x • upperRootMatrix hp
  val_inv := by
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, smul_mul_smul_comm,
      upperRootMatrix_mul_self, smul_zero, add_zero]
    abel
  inv_val := by
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm,
      upperRootMatrix_mul_self, smul_zero, add_zero]
    abel

@[simp]
theorem upperRootElement_val (x : ℝ) :
    (upperRootElement hp x : Matrix (Fin n) (Fin n) ℝ) = 1 + x • upperRootMatrix hp :=
  rfl

theorem upperRootElement_add (x y : ℝ) :
    upperRootElement hp x * upperRootElement hp y = upperRootElement hp (x + y) := by
  apply Units.ext
  rw [Units.val_mul, upperRootElement_val, upperRootElement_val, upperRootElement_val, add_mul,
    mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, upperRootMatrix_mul_self,
    smul_zero, add_zero, add_smul]
  abel

theorem upperRootElement_zero : upperRootElement hp 0 = 1 := by
  apply Units.ext
  simp

theorem upperRootElement_mem (x : ℝ) : upperRootElement hp x ∈ upperUnipotent n ℝ := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 + x • upperRootMatrix hp) i j = 0
    have hne : i ≠ j := fun h => (lt_irrefl _ (h ▸ hij))
    simp only [upperRootMatrix, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul, zero_add]
    rw [ite_eq_right, mul_zero]
    rintro ⟨rfl, rfl⟩
    simp [idxP, idxQ, Fin.lt_def] at hij
  · change (1 + x • upperRootMatrix hp) i i = 1
    simp only [upperRootMatrix, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    rw [ite_eq_right, mul_zero, add_zero]
    rintro ⟨rfl, h⟩
    exact idxP_ne_idxQ hp h.symm

/-- **The torus.** `e(t) diag(a) = diag(a) e((a_p / a_{p+1}) t)`. -/
theorem lowerRootElement_mul_diagonalUnits (a : Fin n → ℝˣ) (t : ℝ) :
    lowerRootElement n p hp t * Iwasawa.diagonalUnits a =
      Iwasawa.diagonalUnits a *
        lowerRootElement n p hp ((a (idxP hp) : ℝ) / a (idxQ hp) * t) := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, lowerRootElement_val, Iwasawa.diagonalUnits_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.add_apply, Matrix.smul_apply, lowerRootMatrix_eq,
    Matrix.single_apply, Matrix.one_apply, smul_eq_mul]
  have ha : (a (idxQ hp) : ℝ) ≠ 0 := (a (idxQ hp)).ne_zero
  by_cases h : idxQ hp = i ∧ idxP hp = j
  · obtain ⟨rfl, rfl⟩ := h
    simp only [idxQ_ne_idxP hp, and_self, ite_true, ite_false]
    field_simp
    ring
  · simp only [h, ite_false, mul_zero, add_zero]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

/-- Entries of `e(t) N e(-t)`. -/
theorem conj_lowerRoot_apply (N : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (i j : Fin n) :
    ((1 + t • lowerRootMatrix n p hp) * N * (1 - t • lowerRootMatrix n p hp)) i j =
      N i j + t * (if i = idxQ hp then N (idxP hp) j else 0) -
        t * (if j = idxP hp then
          N i (idxQ hp) + t * (if i = idxQ hp then N (idxP hp) (idxQ hp) else 0) else 0) := by
  rw [add_mul, one_mul, smul_mul_assoc, mul_sub, mul_one, mul_smul_comm, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  have hEN : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n),
      (lowerRootMatrix n p hp * M) a b = if a = idxQ hp then M (idxP hp) b else 0 := by
    intro M a b
    rw [lowerRootMatrix_eq]
    split_ifs with ha
    · subst ha
      rw [Matrix.single_mul_apply_same, one_mul]
    · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ ha M
  have hNE : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n),
      (M * lowerRootMatrix n p hp) a b = if b = idxP hp then M a (idxQ hp) else 0 := by
    intro M a b
    rw [lowerRootMatrix_eq]
    split_ifs with hb
    · subst hb
      rw [Matrix.mul_single_apply_same, mul_one]
    · exact Matrix.mul_single_apply_of_ne _ _ _ _ _ hb M
  rw [hEN, hNE]
  split_ifs <;> simp [Matrix.add_apply, Matrix.smul_apply, *]

/-- **The unipotent radical.** If `N` is upper unipotent with vanishing `(p, p+1)` entry, then
`e(t) N e(-t)` is upper unipotent. -/
theorem conj_mem_upperUnipotent {N : Langlands.GeneralLinear n ℝ} (hN : N ∈ upperUnipotent n ℝ)
    (hN3 : (N : Matrix (Fin n) (Fin n) ℝ) (idxP hp) (idxQ hp) = 0) (t : ℝ) :
    lowerRootElement n p hp t * N * lowerRootElement n p hp (-t) ∈ upperUnipotent n ℝ := by
  have hval : ((lowerRootElement n p hp t * N * lowerRootElement n p hp (-t) :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      (1 + t • lowerRootMatrix n p hp) * (N : Matrix (Fin n) (Fin n) ℝ) *
        (1 - t • lowerRootMatrix n p hp) := by
    rw [Units.val_mul, Units.val_mul, lowerRootElement_val, lowerRootElement_val, neg_smul,
      ← sub_eq_add_neg]
  have hlow : ∀ i j : Fin n, j < i → (N : Matrix (Fin n) (Fin n) ℝ) i j = 0 :=
    fun i j h => hN.1 h
  have hdiag : ∀ i : Fin n, (N : Matrix (Fin n) (Fin n) ℝ) i i = 1 := hN.2
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change ((lowerRootElement n p hp t * N * lowerRootElement n p hp (-t) :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i j = 0
    rw [hval, conj_lowerRoot_apply, hlow i j hij]
    have hij' : (j : ℕ) < i := hij
    by_cases hi : i = idxQ hp
    · subst hi
      by_cases hj : j = idxP hp
      · subst hj
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, hdiag, hdiag, hN3]
        ring
      · have hjp : j < idxP hp := by
          rw [Fin.lt_def]
          have h1 : (j : ℕ) ≠ p := fun h => hj (Fin.ext h)
          simp only [idxQ, idxP] at hij' ⊢
          omega
        rw [ite_eq_left rfl, ite_eq_right hj, hlow _ _ hjp]
        ring
    · rw [ite_eq_right hi]
      by_cases hj : j = idxP hp
      · subst hj
        have hiq : idxQ hp < i := by
          rw [Fin.lt_def]
          have h1 : (i : ℕ) ≠ p + 1 := fun h => hi (Fin.ext h)
          simp only [idxQ, idxP] at hij' ⊢
          omega
        rw [ite_eq_left rfl, ite_eq_right hi, hlow _ _ hiq]
        ring
      · rw [ite_eq_right hj]
        ring
  · change ((lowerRootElement n p hp t * N * lowerRootElement n p hp (-t) :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i i = 1
    rw [hval, conj_lowerRoot_apply, hdiag]
    by_cases hi : i = idxQ hp
    · subst hi
      rw [ite_eq_left rfl, ite_eq_right (idxQ_ne_idxP hp), hN3]
      ring
    · rw [ite_eq_right hi]
      by_cases hj : i = idxP hp
      · subst hj
        rw [ite_eq_left rfl, ite_eq_right hi, hN3]
        ring
      · rw [ite_eq_right hj]
        ring

/-- **Decomposition of the upper unipotent group.** Every upper unipotent `u` is `N · (1 + x
E_{p,p+1})` with `N` upper unipotent and `N_{p,p+1} = 0`. -/
theorem exists_upperUnipotent_decomp (u : upperUnipotent n ℝ) :
    ∃ (N : Langlands.GeneralLinear n ℝ) (x : ℝ), N ∈ upperUnipotent n ℝ ∧
      (N : Matrix (Fin n) (Fin n) ℝ) (idxP hp) (idxQ hp) = 0 ∧
        (u : Langlands.GeneralLinear n ℝ) = N * upperRootElement hp x := by
  set x : ℝ := ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) (idxP hp) (idxQ hp)
  refine ⟨(u : Langlands.GeneralLinear n ℝ) * upperRootElement hp (-x), x,
    (upperUnipotent n ℝ).mul_mem u.2 (upperRootElement_mem hp _), ?_, ?_⟩
  · rw [Units.val_mul, upperRootElement_val, mul_add, mul_one, mul_smul_comm, Matrix.add_apply,
      Matrix.smul_apply, upperRootMatrix, Matrix.mul_single_apply_same, mul_one, smul_eq_mul]
    have hd : ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) (idxP hp) (idxP hp)
        = 1 := u.2.2 _
    rw [hd]
    ring
  · rw [mul_assoc, upperRootElement_add, neg_add_cancel, upperRootElement_zero, mul_one]

theorem lowerRootElement_zero : lowerRootElement n p hp 0 = 1 := by
  apply Units.ext
  simp

/-- **The root group.** For `y = 1 + t x ≠ 0`,
`e(t) (1 + x E_{p,p+1}) = diag(y⁻¹ at p, y at p+1) (1 + x y E_{p,p+1}) e(t / y)`. -/
theorem lowerRootElement_mul_upperRootElement (x t : ℝ) (hy : 1 + t * x ≠ 0) :
    lowerRootElement n p hp t * upperRootElement hp x =
      Iwasawa.diagonalUnits (Pi.mulSingle (idxP hp) (Units.mk0 (1 + t * x) hy)⁻¹ *
          Pi.mulSingle (idxQ hp) (Units.mk0 (1 + t * x) hy)) *
        upperRootElement hp (x * (1 + t * x)) * lowerRootElement n p hp (t / (1 + t * x)) := by
  have hL : (1 + t • lowerRootMatrix n p hp) * (1 + x • upperRootMatrix hp) =
      1 + t • lowerRootMatrix n p hp + x • upperRootMatrix hp +
        (t * x) • Matrix.single (idxQ hp) (idxQ hp) (1 : ℝ) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm,
      lowerRootMatrix_eq, upperRootMatrix, Matrix.single_mul_single_same, mul_one]
    abel
  have hR : (1 + (x * (1 + t * x)) • upperRootMatrix hp) *
      (1 + (t / (1 + t * x)) • lowerRootMatrix n p hp) =
      1 + (x * (1 + t * x)) • upperRootMatrix hp + (t / (1 + t * x)) • lowerRootMatrix n p hp +
        (x * (1 + t * x) * (t / (1 + t * x))) • Matrix.single (idxP hp) (idxP hp) (1 : ℝ) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm,
      lowerRootMatrix_eq, upperRootMatrix, Matrix.single_mul_single_same, mul_one]
    abel
  have hy' : 1 + x * t ≠ 0 := by rwa [mul_comm]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, mul_assoc, lowerRootElement_val,
    upperRootElement_val, upperRootElement_val, lowerRootElement_val, hL, hR,
    Iwasawa.diagonalUnits_val]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.single_apply, smul_eq_mul, lowerRootMatrix_eq, upperRootMatrix, Pi.mul_apply,
    Units.val_mul, Pi.mulSingle_apply]
  have hP := idxP_ne_idxQ hp
  have hQ := idxQ_ne_idxP hp
  by_cases hi1 : i = idxP hp
  · subst hi1
    by_cases hj1 : j = idxP hp
    · subst hj1
      simp [hP, hQ]
      field_simp
    · by_cases hj2 : j = idxQ hp
      · subst hj2
        simp [hP, hQ]
        field_simp
      · simp [hP, hQ, Ne.symm hj1, Ne.symm hj2]
  · by_cases hi2 : i = idxQ hp
    · subst hi2
      by_cases hj1 : j = idxP hp
      · subst hj1
        simp [hP, hQ]
        field_simp
      · by_cases hj2 : j = idxQ hp
        · subst hj2
          simp [hP, hQ]
        · simp [hP, hQ, Ne.symm hj1, Ne.symm hj2]
    · simp [hi1, hi2, Ne.symm hi1, Ne.symm hi2]

end Matrices

/-! ## The character of the principal series on the two positions -/

section Character

open Langlands.GeneralLinear

variable {n p : ℕ} (hp : p + 1 < n)

/-- With `χ_{p+1}(x) = x^k χ_p(x)` for `x > 0`, the character at `u > 0` placed at `p + 1` is
`u^(k-1)` times the character at `u` placed at `p`. -/
theorem principalSeriesCharacter_mulSingle_idxQ {χ : ℕ → ℝˣ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hχ : ∀ x : ℝˣ, 0 < (x : ℝ) → χ (p + 1) x = ((x : ℝ) : ℂ) ^ k * χ p x) (u : ℝˣ)
    (hu : 0 < (u : ℝ)) :
    principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxQ hp) u) =
      ((u : ℝ) : ℂ) ^ (k - 1) * principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxP hp) u) := by
  unfold principalSeriesCharacter
  rw [← Equiv.prod_comp (Equiv.swap (idxP hp) (idxQ hp))]
  have hfac : ((u : ℝ) : ℂ) ^ (k - 1) = ∏ i : Fin n,
      (if i = idxP hp then ((u : ℝ) : ℂ) ^ (k - 1) else 1) := by
    rw [Fintype.prod_ite_eq']
  rw [hfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hP := idxP_ne_idxQ hp
  have hQ := idxQ_ne_idxP hp
  have hu0 : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  by_cases hi1 : i = idxP hp
  · subst hi1
    rw [Equiv.swap_apply_left, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, ite_eq_left rfl]
    have hq : ((idxQ hp : Fin n) : ℕ) = p + 1 := rfl
    have hp' : ((idxP hp : Fin n) : ℕ) = p := rfl
    rw [hq, hp', hχ u hu, Module.finrank_self, pow_one, Real.norm_of_nonneg hu.le]
    have hexp : ((n : ℂ) - 1) / 2 - ((p + 1 : ℕ) : ℂ) = (((n : ℂ) - 1) / 2 - (p : ℂ)) - 1 := by
      push_cast
      ring
    rw [hexp, Complex.cpow_sub _ _ hu0, Complex.cpow_one]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  · by_cases hi2 : i = idxQ hp
    · subst hi2
      rw [Equiv.swap_apply_right, Pi.mulSingle_eq_of_ne hP, Pi.mulSingle_eq_of_ne hQ,
        ite_eq_right hQ, one_mul]
      have hq : ((idxQ hp : Fin n) : ℕ) = p + 1 := rfl
      have hp' : ((idxP hp : Fin n) : ℕ) = p := rfl
      rw [hq, hp', hχ 1 (by simp)]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne hi1 hi2, Pi.mulSingle_eq_of_ne hi2,
        Pi.mulSingle_eq_of_ne hi1, ite_eq_right hi1, one_mul]

end Character

/-! ## Orbit functions of a principal-series function -/

section Orbit

open Langlands.GeneralLinear

variable {n p : ℕ} (hp : p + 1 < n) {χ : ℕ → ℝˣ → ℂ} {h : Langlands.GeneralLinear n ℝ → ℂ}

theorem covariance_diagonal (hmem : h ∈ principalSeries ℝ n χ) (a : Fin n → ℝˣ)
    (z : Langlands.GeneralLinear n ℝ) :
    h (Iwasawa.diagonalUnits a * z) = principalSeriesCharacter ℝ n χ a * h z := by
  have := hmem.2 a 1 z
  simpa using this

theorem covariance_unipotent (hmem : h ∈ principalSeries ℝ n χ) {N : Langlands.GeneralLinear n ℝ}
    (hN : N ∈ upperUnipotent n ℝ) (z : Langlands.GeneralLinear n ℝ) :
    h (N * z) = principalSeriesCharacter ℝ n χ 1 * h z := by
  have := hmem.2 1 ⟨N, hN⟩ z
  simpa using this

theorem orbitFun_diagonalUnits (hmem : h ∈ principalSeries ℝ n χ) (a : Fin n → ℝˣ)
    (g : Langlands.GeneralLinear n ℝ) :
    orbitFun hp h (Iwasawa.diagonalUnits a * g) = fun t =>
      principalSeriesCharacter ℝ n χ a *
        orbitFun hp h g ((a (idxP hp) : ℝ) / a (idxQ hp) * t) := by
  funext t
  simp only [orbitFun]
  rw [← mul_assoc, lowerRootElement_mul_diagonalUnits, mul_assoc, covariance_diagonal hmem]

theorem orbitFun_unipotent (hmem : h ∈ principalSeries ℝ n χ) {N : Langlands.GeneralLinear n ℝ}
    (hN : N ∈ upperUnipotent n ℝ) (hN3 : (N : Matrix (Fin n) (Fin n) ℝ) (idxP hp) (idxQ hp) = 0)
    (g : Langlands.GeneralLinear n ℝ) :
    orbitFun hp h (N * g) = fun t => principalSeriesCharacter ℝ n χ 1 * orbitFun hp h g t := by
  funext t
  simp only [orbitFun]
  have hre : lowerRootElement n p hp t * (N * g) =
      (lowerRootElement n p hp t * N * lowerRootElement n p hp (-t)) *
        (lowerRootElement n p hp t * g) := by
    rw [mul_assoc (lowerRootElement n p hp t * N), ← mul_assoc (lowerRootElement n p hp (-t)),
      lowerRootElement_add, neg_add_cancel, lowerRootElement_zero, one_mul, mul_assoc]
  rw [hre, covariance_unipotent hmem (conj_mem_upperUnipotent hp hN hN3 t)]

/-- **The root group on orbit functions.** For `1 + t x > 0`,
`h(e(t) (1 + x E_{p,p+1}) g) = (1 + t x)^(k-1) h(e(t / (1 + t x)) g)`. -/
theorem orbitFun_upperRoot (hmem : h ∈ principalSeries ℝ n χ) {k : ℕ} (hk : 1 ≤ k)
    (hχ : ∀ x : ℝˣ, 0 < (x : ℝ) → χ (p + 1) x = ((x : ℝ) : ℂ) ^ k * χ p x) (x : ℝ)
    (g : Langlands.GeneralLinear n ℝ) (t : ℝ) (hy : 0 < 1 + t * x) :
    orbitFun hp h (upperRootElement hp x * g) t =
      (((1 + t * x) ^ (k - 1) : ℝ) : ℂ) * orbitFun hp h g (t / (1 + t * x)) := by
  simp only [orbitFun]
  set y : ℝˣ := Units.mk0 (1 + t * x) hy.ne' with hydef
  set z : Langlands.GeneralLinear n ℝ := lowerRootElement n p hp (t / (1 + t * x)) * g
  have hdec : lowerRootElement n p hp t * (upperRootElement hp x * g) =
      Iwasawa.diagonalUnits (Pi.mulSingle (idxP hp) y⁻¹) *
        (Iwasawa.diagonalUnits (Pi.mulSingle (idxQ hp) y) *
          (upperRootElement hp (x * (1 + t * x)) * z)) := by
    rw [← mul_assoc, lowerRootElement_mul_upperRootElement hp x t hy.ne', map_mul]
    simp only [z, mul_assoc]
    rfl
  have h2 : h (Iwasawa.diagonalUnits (Pi.mulSingle (idxQ hp) y) *
      (upperRootElement hp (x * (1 + t * x)) * z)) =
      principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxQ hp) y) * h z := by
    have := hmem.2 (Pi.mulSingle (idxQ hp) y) ⟨_, upperRootElement_mem hp (x * (1 + t * x))⟩ z
    rwa [mul_assoc] at this
  have hy' : 0 < (y : ℝ) := by simpa [hydef] using hy
  have h3 : principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxP hp) y⁻¹) *
      (principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxP hp) y) * h z) = h z := by
    rw [← covariance_diagonal hmem, ← covariance_diagonal hmem, ← mul_assoc, ← map_mul,
      ← Pi.mulSingle_mul, inv_mul_cancel, Pi.mulSingle_one, map_one, one_mul]
  rw [hdec, covariance_diagonal hmem, h2,
    principalSeriesCharacter_mulSingle_idxQ hp hk hχ y hy']
  calc principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxP hp) y⁻¹) *
        (((y : ℝ) : ℂ) ^ (k - 1) * principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxP hp) y) *
          h z)
      = ((y : ℝ) : ℂ) ^ (k - 1) * (principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxP hp) y⁻¹) *
          (principalSeriesCharacter ℝ n χ (Pi.mulSingle (idxP hp) y) * h z)) := by ring
    _ = (((1 + t * x) ^ (k - 1) : ℝ) : ℂ) * h z := by
        rw [h3, hydef, Units.val_mk0]
        push_cast
        ring

end Orbit

end RealTaylorLeftPolynomialProof

open RealTaylorLeftPolynomialProof in
/-- **Proof of `RealTaylorLeftPolynomialStatement`.** -/
theorem realTaylorLeftPolynomial : RealTaylorLeftPolynomialStatement := by
  intro n χ p k hp hχ h hmem hK g
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : h = 0 := eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact hmem fun κ hκ => by
      have := hK κ hκ
      simp only [Function.iterate_zero, id] at this
      change h (1 * κ) = 0 at this
      rwa [one_mul] at this
    exact ⟨0, by simp, fun t => by simp [h0]⟩
  have hk1 : 1 ≤ k := hk
  have hcd : ∀ z, ContDiff ℝ k (orbitFun hp h z) := fun z =>
    contDiff_infty.mp (contDiff_orbitFun hp hmem.1 z) k
  have hH : ∀ z, iteratedDeriv k (orbitFun hp h z) 0 = 0 := by
    intro z
    obtain ⟨a, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact z
    obtain ⟨N, x, hN, hN3, hu⟩ := exists_upperUnipotent_decomp hp u
    have h1 : iteratedDeriv k (orbitFun hp h κ) 0 = 0 := by
      rw [← iterate_rightDerivative_rightTranslation hp hmem.1]
      exact hK κ hκ
    have h2 : iteratedDeriv k (orbitFun hp h (upperRootElement hp x * κ)) 0 = 0 := by
      have hlim : Tendsto (fun t : ℝ => 1 + t * x) (𝓝 0) (𝓝 1) := by
        have hc : Continuous fun t : ℝ => 1 + t * x := by fun_prop
        simpa using hc.tendsto 0
      have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + t * x := hlim.eventually (lt_mem_nhds one_pos)
      have hev : orbitFun hp h (upperRootElement hp x * κ) =ᶠ[𝓝 0]
          fun t => (((1 + t * x) ^ (k - 1) : ℝ) : ℂ) * orbitFun hp h κ (t / (1 + t * x)) := by
        filter_upwards [hpos] with t ht
        exact orbitFun_upperRoot hp hmem hk1 hχ x κ t ht
      rw [hev.iteratedDeriv_eq, iteratedDeriv_bol hk1 (hcd κ) x, h1]
    have h3 : iteratedDeriv k (orbitFun hp h (N * (upperRootElement hp x * κ))) 0 = 0 := by
      rw [orbitFun_unipotent hp hmem hN hN3, iteratedDeriv_const_mul_field, h2, mul_zero]
    rw [mul_assoc, hu, mul_assoc, orbitFun_diagonalUnits hp hmem, iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_const_smul (hcd _)]
    simp only [mul_zero]
    rw [h3, smul_zero, mul_zero]
  have hall : ∀ t, iteratedDeriv k (orbitFun hp h g) t = 0 := fun t => by
    rw [iteratedDeriv_orbitFun_shift]
    exact hH _
  exact exists_poly_of_iteratedDeriv_eq_zero (contDiff_orbitFun hp hmem.1 g) hall

end Langlands.Archimedean
