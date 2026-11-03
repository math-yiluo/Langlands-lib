import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalDecay

/-! # Corollary VIII.3.2: integrability of `h ↦ |∫ f₁(h g h⁻¹) f₂(g) dg|` modulo `A_G`

Waldspurger 2003, Corollary VIII.3.2: for `f₁ ∈ °C(G)` and `f₂ ∈ C(G)`,
`∫_{A_G\G} |∫_G f₁(h g h⁻¹) f₂(g) dg| dh < ∞`. The proof covers `A_G\G` by the images of the
cells `K a Γ K`, bounds the inner integral on each cell by Proposition VIII.3.1 (using the
smoothness of `f₁` and `f₂`), bounds the measure of the cell by I.1 (5), and sums over the
lattice of the `a`. This module proves these steps for abstract data, with the cover, the
measure bound, the finiteness of the conjugates and the summability as hypotheses.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u

section Cover

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Countable ι]

/-- A nonnegative function bounded by `s i` on the `i`-th set of a countable cover whose
`i`-th set has measure at most `m i` has integral at most `∑ s i m i`. -/
theorem lintegral_le_tsum_of_cover {F : X → ℝ≥0∞} {Ω : ι → Set X}
    (hcover : ∀ x, ∃ i, x ∈ Ω i) {s m : ι → ℝ≥0∞} (hs : ∀ i, ∀ x ∈ Ω i, F x ≤ s i)
    (hm : ∀ i, μ (Ω i) ≤ m i) : ∫⁻ x, F x ∂μ ≤ ∑' i, s i * m i := by
  have hU : (⋃ i, Ω i) = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (hcover x)
  have hcell : ∀ i, ∫⁻ x in Ω i, F x ∂μ ≤ s i * m i := fun i =>
    calc ∫⁻ x in Ω i, F x ∂μ ≤ ∫⁻ _ in Ω i, s i ∂μ := setLIntegral_mono measurable_const (hs i)
      _ = s i * μ (Ω i) := setLIntegral_const _ _
      _ ≤ s i * m i := by gcongr; exact hm i
  calc ∫⁻ x, F x ∂μ = ∫⁻ x in ⋃ i, Ω i, F x ∂μ := by rw [hU, Measure.restrict_univ]
    _ ≤ ∑' i, ∫⁻ x in Ω i, F x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' i, s i * m i := ENNReal.tsum_le_tsum hcell

/-- The summation step of Corollary VIII.3.2: if `F ≤ C₁ e(i)² (1 + t(i))^{-r}` on the
`i`-th cell, the cell has measure at most `C₂ e(i)^{-2}`, and `∑ (1 + t(i))^{-r}` converges,
then `∫ F < ∞`. For Waldspurger's data `e(a)² = δ_0(a)`, `t(a) = σ(a)`, the measure bound is
I.1 (5), and the series runs over `(Ā⁺_0 ∩ G¹)/(Ā⁺_0 ∩ M_0^1)`. -/
theorem lintegral_lt_top_of_cells {F : X → ℝ≥0∞} {Ω : ι → Set X}
    (hcover : ∀ x, ∃ i, x ∈ Ω i) {e t : ι → ℝ} (he : ∀ i, 0 < e i) (ht : ∀ i, 0 ≤ t i)
    {C₁ C₂ r : ℝ}
    (hs : ∀ i, ∀ x ∈ Ω i, F x ≤ ENNReal.ofReal (C₁ * (e i ^ 2 * (1 + t i) ^ (-r))))
    (hm : ∀ i, μ (Ω i) ≤ ENNReal.ofReal (C₂ * (e i ^ 2)⁻¹))
    (hsum : Summable fun i => (1 + t i) ^ (-r)) : ∫⁻ x, F x ∂μ < ⊤ := by
  set C₁' := max C₁ 0
  set C₂' := max C₂ 0
  have hs' : ∀ i, ∀ x ∈ Ω i, F x ≤ ENNReal.ofReal (C₁' * (e i ^ 2 * (1 + t i) ^ (-r))) :=
    fun i x hx => (hs i x hx).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [ht i]) _))))
  have hm' : ∀ i, μ (Ω i) ≤ ENNReal.ofReal (C₂' * (e i ^ 2)⁻¹) :=
    fun i => (hm i).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (sq_nonneg _))))
  refine (lintegral_le_tsum_of_cover hcover hs' hm').trans_lt ?_
  have hterm : ∀ i, ENNReal.ofReal (C₁' * (e i ^ 2 * (1 + t i) ^ (-r))) *
      ENNReal.ofReal (C₂' * (e i ^ 2)⁻¹) = ENNReal.ofReal (C₁' * C₂' * (1 + t i) ^ (-r)) := by
    intro i
    have hei : 0 < e i ^ 2 := pow_pos (he i) 2
    rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _)
      (mul_nonneg hei.le (Real.rpow_nonneg (by linarith [ht i]) _)))]
    congr 1
    calc C₁' * (e i ^ 2 * (1 + t i) ^ (-r)) * (C₂' * (e i ^ 2)⁻¹)
        = C₁' * C₂' * (1 + t i) ^ (-r) * (e i ^ 2 * (e i ^ 2)⁻¹) := by ring
      _ = C₁' * C₂' * (1 + t i) ^ (-r) := by rw [mul_inv_cancel₀ hei.ne', mul_one]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + t i by linarith [ht i]) (-r)
    positivity) (hsum.mul_left (C₁' * C₂'))]
  exact ENNReal.ofReal_lt_top

end Cover

section Conjugates

variable {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G] {M : Subgroup G}
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

/-- The conjugate `g ↦ f(y g y⁻¹)` of a function. -/
def conjFun (y : G) (f : G → ℂ) : G → ℂ :=
  fun g => f (y * g * y⁻¹)

/-- For a left and right invariant measure, `∫ f₁(k a x g x⁻¹ a⁻¹ k⁻¹) f₂(g) dg =
∫ f₁^k(a g a⁻¹) f₂^{x⁻¹}(g) dg`, with `f^y(g) = f(y g y⁻¹)`. -/
theorem integral_conj_mul_conj (f₁ f₂ : G → ℂ) (k a x : G) :
    ∫ g, f₁ ((k * a * x) * g * (k * a * x)⁻¹) * f₂ g ∂μ =
      ∫ g, conjFun k f₁ (a * g * a⁻¹) * conjFun x⁻¹ f₂ g ∂μ := by
  have h := integral_mul_left_eq_self (μ := μ)
    (fun g => f₁ ((k * a * x) * g * (k * a * x)⁻¹) * f₂ g) x⁻¹
  have h' := integral_mul_right_eq_self (μ := μ)
    (fun g => f₁ ((k * a * x) * (x⁻¹ * g) * (k * a * x)⁻¹) * f₂ (x⁻¹ * g)) x
  rw [← h, ← h']
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [conjFun, inv_inv]
  congr 2
  group

omit [MeasurableMul G] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in
/-- Uniform constants for finitely many pairs: if the conclusion of Proposition VIII.3.1
holds for every pair in a finite set, one constant works for all of them. -/
theorem ConjugationIntegralBound.uniform {T : Set M} {e : M → ℝ} {σ : G → ℝ}
    {S : Set ((G → ℂ) × (G → ℂ))} (hS : S.Finite)
    (h : ∀ p ∈ S, ConjugationIntegralBound μ T p.1 p.2 e σ) (r : ℝ) :
    ∃ c : ℝ≥0, ∀ p ∈ S, ∀ a ∈ T,
      ‖∫ g, p.1 ((a : G) * g * (a : G)⁻¹) * p.2 g ∂μ‖ₑ ≤
        c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)) := by
  classical
  choose! c hc using fun p (hp : p ∈ S) => h p hp r
  refine ⟨hS.toFinset.sup c, fun p hp a ha => (hc p hp a ha).trans ?_⟩
  gcongr
  exact Finset.le_sup (hS.mem_toFinset.mpr hp)

end Conjugates

section Corollary

variable {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G] {M : Subgroup G}
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {X : Type*} [MeasurableSpace X] {μX : Measure X} {ι : Type*} [Countable ι]

/-- Waldspurger, Corollary VIII.3.2, for abstract data. Let `π : G → X` be the projection to
the quotient `X` (Waldspurger's `A_G\G`) with measure `μ_X`, and `F : X → ℝ≥0∞` with
`F(π(h)) = |∫ f₁(h g h⁻¹) f₂(g) dμ|`. Assume: cells `Ω(i)` covering `X` such that every point
of `Ω(i)` is `π(k a_i y)` with `k ∈ K'` and `y ∈ Y`; the conjugates `f₁^k` (`k ∈ K'`) and
`f₂^{y^{-1}}` (`y ∈ Y`) form finite sets, and Proposition VIII.3.1
(`ConjugationIntegralBound`) holds on `T` for all these pairs; `a_i ∈ T`; the measure bound
`μ_X(Ω(i)) ≤ C e(a_i)^{-2}`; and the summability of `(1 + σ(a_i))^{-r}` for one `r`. Then
`∫ F dμ_X < ∞`. -/
theorem lintegral_lt_top_of_conjugationIntegralBound {T : Set M} {e : M → ℝ} {σ : G → ℝ}
    (he : ∀ a ∈ T, 0 < e a) (hσ : ∀ g, 0 ≤ σ g) {f₁ f₂ : G → ℂ} {π : G → X}
    {F : X → ℝ≥0∞}
    (hF : ∀ h, F (π h) = ‖∫ g, f₁ (h * g * h⁻¹) * f₂ g ∂μ‖ₑ)
    {Ω : ι → Set X} (hcover : ∀ x, ∃ i, x ∈ Ω i) {a : ι → M} (haT : ∀ i, a i ∈ T)
    {K' Y : Set G}
    (hcell : ∀ i, ∀ x ∈ Ω i, ∃ k ∈ K', ∃ y ∈ Y, x = π (k * a i * y))
    (hfin₁ : (Set.image (fun k => conjFun k f₁) K').Finite)
    (hfin₂ : (Set.image (fun y => conjFun y⁻¹ f₂) Y).Finite)
    (h31 : ∀ k ∈ K', ∀ y ∈ Y, ConjugationIntegralBound μ T (conjFun k f₁) (conjFun y⁻¹ f₂) e σ)
    {C₂ : ℝ} (hm : ∀ i, μX (Ω i) ≤ ENNReal.ofReal (C₂ * (e (a i) ^ 2)⁻¹))
    {r : ℝ} (hsum : Summable fun i => (1 + σ (a i)) ^ (-r)) :
    ∫⁻ x, F x ∂μX < ⊤ := by
  set S : Set ((G → ℂ) × (G → ℂ)) :=
    (Set.image (fun k => conjFun k f₁) K') ×ˢ (Set.image (fun y => conjFun y⁻¹ f₂) Y)
  have hS : S.Finite := hfin₁.prod hfin₂
  have hSb : ∀ p ∈ S, ConjugationIntegralBound μ T p.1 p.2 e σ := by
    rintro ⟨φ₁, φ₂⟩ ⟨⟨k, hk, rfl⟩, ⟨y, hy, rfl⟩⟩
    exact h31 k hk y hy
  obtain ⟨c, hc⟩ := ConjugationIntegralBound.uniform hS hSb r
  refine lintegral_lt_top_of_cells hcover (fun i => he _ (haT i)) (fun i => hσ _)
    (C₁ := c) (r := r) (fun i x hx => ?_) hm hsum
  obtain ⟨k, hk, y, hy, rfl⟩ := hcell i x hx
  rw [hF, integral_conj_mul_conj]
  have := hc (conjFun k f₁, conjFun y⁻¹ f₂) ⟨⟨k, hk, rfl⟩, ⟨y, hy, rfl⟩⟩ (a i) (haT i)
  refine this.trans ?_
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg c), ENNReal.ofReal_coe_nnreal]

end Corollary

end Langlands.HarishChandraSchwartz
