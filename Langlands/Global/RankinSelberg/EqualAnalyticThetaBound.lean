import Langlands.Global.RankinSelberg.EqualAnalyticTheta

/-! # A bound for the theta series in torus coordinates

For a dominated `Ψ`, a compact `Q ⊆ GL_n(𝔸)` and an integer `N > n [F:ℚ]` there is `K` with
`Θ⁺(Ψ, A(x) q) ≤ K exp (-N t)` whenever `t ≤ x_j` for every `j` and `q ∈ Q`
(`exists_thetaNorm_le`). Here `A(x) = diag(e^(x_1), …, e^(x_n))` at every infinite place.

The proof: `Ψ(· q)` is dominated uniformly in `q ∈ Q` (`exists_uniform_dominated`), so only
`ξ ∈ (d⁻¹𝒪)^n` contribute and `|Ψ(ξ A(x) q)| ≤ K₁ (1 + e^t ‖ξ‖_∞)^(-N)`; nonzero lattice
points have `‖ξ‖_∞ ≥ δ > 0` (`exists_pos_le_norm_rowEmbedding`), which gives
`(1 + e^t ‖ξ‖)^(-N) ≤ e^(-N t) (1/δ + 1)^N (1 + ‖ξ‖)^(-N)`, and the last series converges.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set Filter Topology
open scoped Classical Matrix ENNReal

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

/-- The archimedean coordinates of `x M`, with an explicit constant. -/
theorem norm_archimedeanCoordinates_mul_le' (n : ℕ) (M : Matrix (Fin n) (Fin n) (Adeles F))
    (x : RowVector F n) :
    ‖archimedeanCoordinates F n (x * M)‖ ≤
      (∑ i, ∑ j, ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖) *
        ‖archimedeanCoordinates F n x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [archimedeanCoordinates_mul]
  calc ‖∑ i, archimedeanCoordinates F n x i *
        InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖
      ≤ ∑ i, ‖archimedeanCoordinates F n x i‖ *
        ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_mul_le _ _)
    _ ≤ ∑ i, ‖archimedeanCoordinates F n x‖ *
        ∑ j, ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul (norm_le_pi_norm _ i)
          (Finset.single_le_sum (f := fun j => ‖InfiniteAdeleRing.ringEquiv_mixedSpace F
            (M i j).1‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j))
          (norm_nonneg _) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖) *
        ‖archimedeanCoordinates F n x‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- The archimedean size of `q⁻¹`. -/
def invArchSize (n : ℕ) (q : AdelicGL F n) : ℝ :=
  ∑ i, ∑ j, ‖InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j).1)‖

theorem continuous_inv_entry (n : ℕ) (i j : Fin n) :
    Continuous fun q : AdelicGL F n => ((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j :=
  (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Adeles F))).matrix_elem i j

theorem continuous_invArchSize (n : ℕ) : Continuous (invArchSize F n) := by
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have hrow : Continuous fun q : AdelicGL F n => (Matrix.of fun (_ : Fin 1) (j' : Fin n) =>
      ((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j' : RowVector F n) :=
    continuous_matrix fun _ j' => continuous_inv_entry F n i j'
  exact ((continuous_apply j).comp ((continuous_archimedeanCoordinates F n).comp hrow)).norm

omit [NumberField F] in
/-- An elementary inequality: `A ≤ B Z` and `(1 + Z)^N P ≤ K` give `(1 + A)^N P ≤ (1 + B)^N K`. -/
theorem pow_mul_le_aux {A Z P B K₀ : ℝ} (N : ℕ) (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Z) (hP0 : 0 ≤ P)
    (hB0 : 0 ≤ B) (hAZ : A ≤ B * Z) (hK : (1 + Z) ^ N * P ≤ K₀) :
    (1 + A) ^ N * P ≤ (1 + B) ^ N * K₀ := by
  have h1 : 1 + A ≤ (1 + B) * (1 + Z) := by nlinarith
  calc (1 + A) ^ N * P ≤ ((1 + B) * (1 + Z)) ^ N * P :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) h1 N) hP0
    _ = (1 + B) ^ N * ((1 + Z) ^ N * P) := by rw [mul_pow]; ring
    _ ≤ (1 + B) ^ N * K₀ := mul_le_mul_of_nonneg_left hK (by positivity)

/-- **Uniform domination of right translates by a compact set.** -/
theorem exists_uniform_dominated (n : ℕ) {Ψ : RowVector F n → ℂ} (hΨ : IsRowDominated F n Ψ)
    {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) (N : ℕ) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ K : ℝ,
      (∀ (y : RowVector F n) (q : AdelicGL F n), q ∈ Q →
        Ψ (y * (q : Matrix (Fin n) (Fin n) (Adeles F))) ≠ 0 → ∀ j,
          algebraMap (𝓞 F) (FiniteAdeles F) d * finiteCoordinates F n y j ∈
            integralFiniteAdeles F) ∧
      ∀ (y : RowVector F n) (q : AdelicGL F n), q ∈ Q →
        (1 + ‖archimedeanCoordinates F n y‖) ^ N *
          ‖Ψ (y * (q : Matrix (Fin n) (Fin n) (Adeles F)))‖ ≤ K := by
  obtain ⟨d₀, hd₀, hsupp, hdec⟩ := hΨ
  have hKf : IsCompact (⋃ p : Fin n × Fin n,
      (fun q : AdelicGL F n => (((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))
        p.1 p.2).2) '' Q) := isCompact_iUnion fun p =>
    hQ.image (continuous_snd.comp (continuous_inv_entry F n p.1 p.2))
  obtain ⟨e₀, he₀, hes⟩ := exists_integer_mul_mem_of_isCompact F hKf
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn (continuous_invArchSize F n).continuousOn
  obtain ⟨K₀, hK₀⟩ := hdec N
  have hinv : ∀ (y : RowVector F n) (q : AdelicGL F n),
      y * (q : Matrix (Fin n) (Fin n) (Adeles F)) *
        ((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) = y := by
    intro y q
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine ⟨d₀ * e₀, mul_ne_zero hd₀ he₀, (1 + |B|) ^ N * K₀, fun y q hq hy j => ?_,
    fun y q hq => ?_⟩
  · have h1 := hsupp _ hy
    rw [← hinv y q, finiteCoordinates_mul, Finset.mul_sum]
    refine sum_mem fun i _ => ?_
    have : algebraMap (𝓞 F) (FiniteAdeles F) (d₀ * e₀) *
        (finiteCoordinates F n (y * (q : Matrix (Fin n) (Fin n) (Adeles F))) i *
          (((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j).2) =
        (algebraMap (𝓞 F) (FiniteAdeles F) d₀ *
          finiteCoordinates F n (y * (q : Matrix (Fin n) (Fin n) (Adeles F))) i) *
        (algebraMap (𝓞 F) (FiniteAdeles F) e₀ *
          (((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j).2) := by
      rw [map_mul]
      ring
    rw [this]
    exact mul_mem (h1 i) (hes _ (mem_iUnion.2 ⟨(i, j), q, hq, rfl⟩))
  · have hx := norm_archimedeanCoordinates_mul_le' F n
      ((q⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))
      (y * (q : Matrix (Fin n) (Fin n) (Adeles F)))
    rw [hinv] at hx
    have hsz : invArchSize F n q ≤ |B| := by
      have h0 : 0 ≤ invArchSize F n q := by unfold invArchSize; positivity
      have := hB q hq
      rw [Real.norm_eq_abs, abs_of_nonneg h0] at this
      exact this.trans (le_abs_self B)
    exact pow_mul_le_aux N (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (abs_nonneg B)
      (hx.trans (mul_le_mul_of_nonneg_right hsz (norm_nonneg _))) (hK₀ _)

theorem rowEmbedding_ne_zero (n : ℕ) {ξ : Fin n → F} (hξ : ξ ≠ 0) : rowEmbedding F n ξ ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hξ
  intro h
  have h' := congrFun h j
  exact (map_ne_zero (mixedEmbedding F)).2 hj h'

/-- If `Σ (1 + a i)^(-r)` converges and `a` is positive away from `z`, then `a` is bounded
below by a positive constant away from `z`. -/
theorem exists_pos_le_of_summable {ι : Type*} (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (z : ι)
    (hpos : ∀ i, i ≠ z → 0 < a i) {r : ℝ} (hr : 0 < r)
    (hs : Summable fun i => (1 + a i) ^ (-r)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, i ≠ z → δ ≤ a i := by
  have hfin : {i | a i ≤ 1}.Finite := by
    have hev : ∀ᶠ i in cofinite, (1 + a i) ^ (-r) < (2 : ℝ) ^ (-r) :=
      hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (by positivity))
    refine (Filter.eventually_cofinite.1 hev).subset fun i hi => ?_
    have hi' : a i ≤ 1 := hi
    have h0 := ha0 i
    show ¬ (1 + a i) ^ (-r) < (2 : ℝ) ^ (-r)
    exact not_lt.2 (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith))
  classical
  by_cases hT : (hfin.toFinset.filter (fun i => i ≠ z)).Nonempty
  · obtain ⟨i₀, hi₀, hmin⟩ := (hfin.toFinset.filter (fun i => i ≠ z)).exists_min_image a hT
    have hpos₀ : 0 < a i₀ := hpos i₀ (Finset.mem_filter.1 hi₀).2
    refine ⟨min 1 (a i₀), lt_min one_pos hpos₀, fun i hne => ?_⟩
    by_cases h1 : a i ≤ 1
    · exact (min_le_right _ _).trans
        (hmin i (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 h1, hne⟩))
    · exact (min_le_left _ _).trans (le_of_lt (not_le.1 h1))
  · refine ⟨1, one_pos, fun i hne => ?_⟩
    by_contra h
    exact hT ⟨i, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 (le_of_lt (not_le.1 h)), hne⟩⟩

omit [NumberField F] in
theorem zero_mem_integralRows (n : ℕ) (D : 𝓞 F) : (0 : Fin n → F) ∈ IntegralRows F n D :=
  fun _ => ⟨0, by simp⟩

/-- **Nonzero lattice points are bounded away from zero.** -/
theorem exists_pos_le_norm_rowEmbedding (n : ℕ) (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ ∈ IntegralRows F n D, ξ ≠ 0 → δ ≤ ‖rowEmbedding F n ξ‖ := by
  have hr : ((n * Module.finrank ℚ F : ℕ) : ℝ) < ((n * Module.finrank ℚ F : ℕ) : ℝ) + 1 :=
    lt_add_one _
  have hs := summable_integralRows F n D hD hr
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_of_summable
    (fun ξ : IntegralRows F n D => ‖rowEmbedding F n ξ.1‖) (fun _ => norm_nonneg _)
    ⟨0, zero_mem_integralRows F n D⟩
    (fun ξ hξ => norm_pos_iff.2 (rowEmbedding_ne_zero F n fun h => hξ (Subtype.ext h)))
    (by positivity) hs
  exact ⟨δ, hδ, fun ξ hξ hne => hle ⟨ξ, hξ⟩ fun h => hne (congrArg Subtype.val h)⟩

/-! ### The bound -/

theorem archimedeanCoordinates_ratRow_mul_torInf (n : ℕ) (C : RatRow F n) (x : Fin n → ℝ)
    (j : Fin n) :
    archimedeanCoordinates F n (ratRow F n C * ((AdelicGL.ofInfinite F n (torInf F n x) :
        AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))) j =
      Real.exp (x j) • mixedEmbedding F (C 0 j) := by
  have h := congrArg (fun p => p.1 j)
    (rowSplit_rightMul_torInf F n x (ratRow F n C))
  simp only at h
  change archimedeanCoordinates F n
    (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x)) (ratRow F n C)) j = _
  rw [show archimedeanCoordinates F n
      (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x)) (ratRow F n C)) j =
    (rowSplit F n (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x)) (ratRow F n C))).1 j
    from rfl, h, scaleRow_apply]
  congr 1
  exact congrFun (archimedeanCoordinates_ratRow F n C) j

theorem finiteCoordinates_ratRow_mul_torInf (n : ℕ) (C : RatRow F n) (x : Fin n → ℝ)
    (j : Fin n) :
    finiteCoordinates F n (ratRow F n C * ((AdelicGL.ofInfinite F n (torInf F n x) :
        AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))) j =
      algebraMap F (FiniteAdeles F) (C 0 j) := by
  have h := congrArg (fun p => p.2 j)
    (rowSplit_rightMul_torInf F n x (ratRow F n C))
  simp only at h
  change (rowSplit F n (rightMul F n (AdelicGL.ofInfinite F n (torInf F n x))
    (ratRow F n C))).2 j = _
  rw [h]
  exact finiteCoordinates_ratRow F n C j

/-- The lattice weight `(1 + ‖ξ‖)^(-N)` on `(d⁻¹𝒪)^n`, zero elsewhere. -/
def latticeWeight (n : ℕ) (d : 𝓞 F) (N : ℕ) (C : RatRow F n) : ℝ :=
  (IntegralRows F n d).indicator (fun ξ => (1 + ‖rowEmbedding F n ξ‖) ^ (-(N : ℝ)))
    (ratRowVec F n C)

theorem latticeWeight_nonneg (n : ℕ) (d : 𝓞 F) (N : ℕ) (C : RatRow F n) :
    0 ≤ latticeWeight F n d N C :=
  Set.indicator_nonneg (fun ξ _ => by positivity) _

theorem summable_latticeWeight (n : ℕ) (d : 𝓞 F) (hd : d ≠ 0) (N : ℕ)
    (hN : n * Module.finrank ℚ F < N) : Summable (latticeWeight F n d N) := by
  have hr : ((n * Module.finrank ℚ F : ℕ) : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hv : Summable ((IntegralRows F n d).indicator
      fun ξ => (1 + ‖rowEmbedding F n ξ‖) ^ (-(N : ℝ))) :=
    summable_subtype_iff_indicator.1 (summable_integralRows F n d hd hr)
  exact hv.comp_injective (ratRowVec_injective F n)

/-- An elementary inequality behind the theta bound. -/
theorem real_bound_aux {P K₁ X a δ t : ℝ} (N : ℕ) (hP : P ≤ K₁ * (1 + X) ^ (-(N : ℝ)))
    (hX : 0 ≤ X) (hδ : 0 < δ) (hδa : δ ≤ a) (harch : a ≤ Real.exp (-t) * X) :
    P ≤ |K₁| * (1 / δ + 1) ^ N * Real.exp (-(N * t)) * (1 + a) ^ (-(N : ℝ)) := by
  have ha0 : 0 ≤ a := hδ.le.trans hδa
  have hkey : 1 + a ≤ (1 / δ + 1) * Real.exp (-t) * (1 + X) := by
    have h4 : 1 + a ≤ (1 / δ + 1) * a := by
      have h6 : 1 ≤ a / δ := by rw [le_div_iff₀ hδ]; linarith
      have h5 : (1 / δ + 1) * a = a / δ + a := by field_simp
      rw [h5]; linarith
    have h5 : (1 / δ + 1) * a ≤ (1 / δ + 1) * (Real.exp (-t) * (1 + X)) :=
      mul_le_mul_of_nonneg_left (harch.trans (mul_le_mul_of_nonneg_left (by linarith)
        (Real.exp_pos _).le)) (by positivity)
    linarith
  have hA : (0 : ℝ) < (1 + a) ^ N := by positivity
  have hX' : (0 : ℝ) < (1 + X) ^ N := by positivity
  have hpowA : (1 + X) ^ (-(N : ℝ)) ≤
      ((1 / δ + 1) * Real.exp (-t)) ^ N * (1 + a) ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
      Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hA, inv_mul_le_iff₀ hX']
    calc (1 + a) ^ N ≤ ((1 / δ + 1) * Real.exp (-t) * (1 + X)) ^ N :=
          pow_le_pow_left₀ (by positivity) hkey N
      _ = (1 + X) ^ N * ((1 / δ + 1) * Real.exp (-t)) ^ N := by rw [mul_pow, mul_comm]
  have hexp : ((1 / δ + 1) * Real.exp (-t)) ^ N = (1 / δ + 1) ^ N * Real.exp (-(N * t)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    ring_nf
  rw [hexp] at hpowA
  calc P ≤ K₁ * (1 + X) ^ (-(N : ℝ)) := hP
    _ ≤ |K₁| * (1 + X) ^ (-(N : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |K₁| * ((1 / δ + 1) ^ N * Real.exp (-(N * t)) * (1 + a) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hpowA (abs_nonneg _)
    _ = |K₁| * (1 / δ + 1) ^ N * Real.exp (-(N * t)) * (1 + a) ^ (-(N : ℝ)) := by ring

/-- The pointwise bound for one nonzero rational row. -/
theorem norm_rowMul_torInf_le (n : ℕ) {Ψ : RowVector F n → ℂ} {Q : Set (AdelicGL F n)}
    {d : 𝓞 F} {K₁ δ : ℝ} {N : ℕ}
    (hsupp : ∀ (y : RowVector F n) (q : AdelicGL F n), q ∈ Q →
        Ψ (y * (q : Matrix (Fin n) (Fin n) (Adeles F))) ≠ 0 → ∀ j,
          algebraMap (𝓞 F) (FiniteAdeles F) d * finiteCoordinates F n y j ∈
            integralFiniteAdeles F)
    (hdec : ∀ (y : RowVector F n) (q : AdelicGL F n), q ∈ Q →
        (1 + ‖archimedeanCoordinates F n y‖) ^ N *
          ‖Ψ (y * (q : Matrix (Fin n) (Fin n) (Adeles F)))‖ ≤ K₁)
    (hδ : 0 < δ) (hδle : ∀ ξ ∈ IntegralRows F n d, ξ ≠ 0 → δ ≤ ‖rowEmbedding F n ξ‖)
    (x : Fin n → ℝ) (t : ℝ) (ht : ∀ j, t ≤ x j) (q : AdelicGL F n) (hq : q ∈ Q)
    (C : RatRow F n) (hC : C ≠ 0) :
    ‖Ψ (ratRow F n C * ((AdelicGL.ofInfinite F n (torInf F n x) * q : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)))‖ ≤
      |K₁| * (1 / δ + 1) ^ N * Real.exp (-(N * t)) * latticeWeight F n d N C := by
  obtain ⟨y, hydef⟩ : ∃ y : RowVector F n, y = ratRow F n C *
      ((AdelicGL.ofInfinite F n (torInf F n x) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) := ⟨_, rfl⟩
  have hy : ratRow F n C * ((AdelicGL.ofInfinite F n (torInf F n x) * q : AdelicGL F n) :
      Matrix (Fin n) (Fin n) (Adeles F)) = y * (q : Matrix (Fin n) (Fin n) (Adeles F)) := by
    rw [hydef, Units.val_mul, Matrix.mul_assoc]
  rw [hy]
  by_cases hΨ0 : Ψ (y * (q : Matrix (Fin n) (Fin n) (Adeles F))) = 0
  · rw [hΨ0, norm_zero]
    exact mul_nonneg (by positivity) (latticeWeight_nonneg F n d N C)
  have hmem : ratRowVec F n C ∈ IntegralRows F n d := by
    intro j
    have h1 := hsupp y q hq hΨ0 j
    rw [hydef, finiteCoordinates_ratRow_mul_torInf] at h1
    have h2 : algebraMap (𝓞 F) (FiniteAdeles F) d * algebraMap F (FiniteAdeles F) (C 0 j) =
        algebraMap F (FiniteAdeles F) (algebraMap (𝓞 F) F d * C 0 j) := by
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
    rw [h2] at h1
    obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_integral F _ h1
    exact ⟨a, ha.symm⟩
  have hne : ratRowVec F n C ≠ 0 := by
    intro h
    apply hC
    apply ratRowVec_injective F n
    rw [h]
    rfl
  have harch : ‖rowEmbedding F n (ratRowVec F n C)‖ ≤
      Real.exp (-t) * ‖archimedeanCoordinates F n y‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
    have hj := norm_le_pi_norm (archimedeanCoordinates F n y) j
    rw [hydef, archimedeanCoordinates_ratRow_mul_torInf, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hj
    have hxj : Real.exp t ≤ Real.exp (x j) := Real.exp_le_exp.2 (ht j)
    have hm := norm_nonneg (mixedEmbedding F (C 0 j))
    have h3 : Real.exp t * ‖mixedEmbedding F (C 0 j)‖ ≤ ‖archimedeanCoordinates F n y‖ := by
      rw [← hydef] at hj
      exact (mul_le_mul_of_nonneg_right hxj hm).trans hj
    rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _), mul_comm]
    exact h3
  have hw : latticeWeight F n d N C =
      (1 + ‖rowEmbedding F n (ratRowVec F n C)‖) ^ (-(N : ℝ)) :=
    Set.indicator_of_mem hmem _
  rw [hw]
  exact real_bound_aux N (IsRowDominated.norm_le_rpow (F := F)
    (Φ := fun z => Ψ (z * (q : Matrix (Fin n) (Fin n) (Adeles F)))) (fun z => hdec z q hq) y)
    (norm_nonneg _) hδ (hδle _ hmem hne) harch

/-- **The theta bound in torus coordinates.** -/
theorem exists_thetaNorm_le (n : ℕ) {Ψ : RowVector F n → ℂ} (hΨ : IsRowDominated F n Ψ)
    {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) (N : ℕ) (hN : n * Module.finrank ℚ F < N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : Fin n → ℝ) (t : ℝ), (∀ j, t ≤ x j) → ∀ q ∈ Q,
      thetaNorm F n Ψ (AdelicGL.ofInfinite F n (torInf F n x) * q) ≤
        ENNReal.ofReal (K * Real.exp (-(N * t))) := by
  obtain ⟨d, hd, K₁, hsupp, hdec⟩ := exists_uniform_dominated F n hΨ hQ N
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_rowEmbedding F n d hd
  have hu := summable_latticeWeight F n d hd N hN
  have hS0 : 0 ≤ ∑' C, latticeWeight F n d N C := tsum_nonneg (latticeWeight_nonneg F n d N)
  have hc0 : 0 ≤ |K₁| * (1 / δ + 1) ^ N := by positivity
  refine ⟨|K₁| * (1 / δ + 1) ^ N * ∑' C, latticeWeight F n d N C, mul_nonneg hc0 hS0,
    fun x t ht q hq => ?_⟩
  have hnn : ∀ C, 0 ≤ |K₁| * (1 / δ + 1) ^ N * Real.exp (-(N * t)) * latticeWeight F n d N C :=
    fun C => mul_nonneg (mul_nonneg hc0 (Real.exp_pos _).le) (latticeWeight_nonneg F n d N C)
  calc thetaNorm F n Ψ (AdelicGL.ofInfinite F n (torInf F n x) * q)
      ≤ ∑' C, ENNReal.ofReal
          (|K₁| * (1 / δ + 1) ^ N * Real.exp (-(N * t)) * latticeWeight F n d N C) := by
        refine ENNReal.tsum_le_tsum fun C => ?_
        split_ifs with hC
        · exact zero_le
        · rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_rowMul_torInf_le F n hsupp hdec hδ hδle x t ht q
            hq C hC)
    _ = ENNReal.ofReal (∑' C,
          |K₁| * (1 / δ + 1) ^ N * Real.exp (-(N * t)) * latticeWeight F n d N C) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn (hu.mul_left _)).symm
    _ = ENNReal.ofReal (|K₁| * (1 / δ + 1) ^ N * (∑' C, latticeWeight F n d N C) *
          Real.exp (-(N * t))) := by
        rw [tsum_mul_left]
        ring_nf

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
