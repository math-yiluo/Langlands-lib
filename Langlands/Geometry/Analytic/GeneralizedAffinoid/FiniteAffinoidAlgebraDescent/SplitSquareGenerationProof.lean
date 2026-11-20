import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.SplitSquareGenerationStatement

/-! # Proof of matched generation of finite modules over a split square -/

noncomputable section

universe u v w

open Filter Topology

namespace Langlands.Analytic.BoundedAlgHom.SplitSquareGeneration

/-- An additive continuous map from a complete normed group that admits
approximate solutions with norm control and halving residuals is surjective,
with norm-controlled exact solutions. -/
theorem exists_eq_of_approx {V W : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    [NormedAddCommGroup W] (T : V →+ W) (hT : Continuous T) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ w, ∃ v, ‖v‖ ≤ C * ‖w‖ ∧ ‖w - T v‖ ≤ ‖w‖ / 2) (w : W) :
    ∃ v, T v = w ∧ ‖v‖ ≤ C * ‖w‖ * 2 := by
  choose f hf₁ hf₂ using h
  let res : ℕ → W := fun k => (fun z => z - T (f z))^[k] w
  have res_succ : ∀ k, res (k + 1) = res k - T (f (res k)) := fun k =>
    Function.iterate_succ_apply' _ k w
  have hres : ∀ k, ‖res k‖ ≤ ‖w‖ * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => simp [res]
    | succ k ih =>
      rw [res_succ, pow_succ]
      calc ‖res k - T (f (res k))‖ ≤ ‖res k‖ / 2 := hf₂ _
        _ ≤ ‖w‖ * (1 / 2) ^ k / 2 := by gcongr
        _ = ‖w‖ * ((1 / 2) ^ k * (1 / 2)) := by ring
  have hbound : ∀ k, ‖f (res k)‖ ≤ C * ‖w‖ * (1 / 2) ^ k := fun k =>
    (hf₁ _).trans (by
      calc C * ‖res k‖ ≤ C * (‖w‖ * (1 / 2) ^ k) := by gcongr; exact hres k
        _ = C * ‖w‖ * (1 / 2) ^ k := by ring)
  have hgeom : HasSum (fun k : ℕ => C * ‖w‖ * (1 / 2) ^ k) (C * ‖w‖ * 2) :=
    hasSum_geometric_two.mul_left _
  have hsum : Summable fun k => f (res k) := Summable.of_norm_bounded hgeom.summable hbound
  refine ⟨∑' k, f (res k), ?_, tsum_of_norm_bounded hgeom hbound⟩
  have hpartial : ∀ N, T (∑ k ∈ Finset.range N, f (res k)) = w - res N := by
    intro N
    rw [map_sum]
    have : ∀ k, T (f (res k)) = res k - res (k + 1) := fun k => by rw [res_succ]; abel
    simp_rw [this]
    rw [Finset.sum_range_sub']
    rfl
  have hlim₁ : Tendsto (fun N => T (∑ k ∈ Finset.range N, f (res k))) atTop
      (𝓝 (T (∑' k, f (res k)))) :=
    (hT.tendsto _).comp hsum.hasSum.tendsto_sum_nat
  have hres0 : Tendsto res atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hres ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul ‖w‖
  have hlim₂ : Tendsto (fun N => T (∑ k ∈ Finset.range N, f (res k))) atTop (𝓝 w) := by
    simp_rw [hpartial]
    simpa using (tendsto_const_nhds (x := w)).sub hres0
  exact tendsto_nhds_unique hlim₁ hlim₂

/-- A uniform bound on a finite sum of products of bounded factors. -/
theorem norm_sum_mul_le {A : Type*} [NormedCommRing A] {n : ℕ} (f g : Fin n → A)
    {α β : ℝ} (hα : 0 ≤ α) (hf : ∀ k, ‖f k‖ ≤ α) (hg : ∀ k, ‖g k‖ ≤ β) :
    ‖∑ k, f k * g k‖ ≤ n * (α * β) := by
  calc ‖∑ k, f k * g k‖ ≤ ∑ k, ‖f k * g k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, α * β := Finset.sum_le_sum fun k _ =>
        (norm_mul_le _ _).trans (mul_le_mul (hf k) (hg k) (norm_nonneg _) hα)
    _ = n * (α * β) := by simp

section RowSolution

variable {A₁ A₂ A₁₂ : Type*} [NormedCommRing A₁] [NormedCommRing A₂] [NormedCommRing A₁₂]
  [CompleteSpace A₁] [CompleteSpace A₂]

/-- Solving one row of the linear Cartan equation
`r₁ a + (r₂ b) (1 + Δ) = t` for a small matrix `Δ`, with norm control on `a`. -/
theorem exists_row_solution (r₁ : A₁ →+* A₁₂) (r₂ : A₂ →+* A₁₂)
    (hr₁ : Continuous r₁) (hr₂ : Continuous r₂) {c L δ : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hsplit : ∀ h, ∃ h₁ h₂, h = r₁ h₁ + r₂ h₂ ∧ ‖h₁‖ ≤ c * ‖h‖ ∧ ‖h₂‖ ≤ c * ‖h‖)
    (hr₂L : ∀ a, ‖r₂ a‖ ≤ L * ‖a‖) {n : ℕ} (Δ : Fin n → Fin n → A₁₂)
    (hΔ : ∀ k j, ‖Δ k j‖ ≤ δ) (hsmall : n * (L * c * δ) ≤ 1 / 2) (t : Fin n → A₁₂) :
    ∃ (a : Fin n → A₁) (b : Fin n → A₂),
      (∀ j, r₁ (a j) + r₂ (b j) + ∑ k, r₂ (b k) * Δ k j = t j) ∧
        ∀ j, ‖a j‖ ≤ c * ‖t‖ * 2 := by
  let T : (Fin n → A₁) × (Fin n → A₂) →+ (Fin n → A₁₂) :=
    { toFun := fun v j => r₁ (v.1 j) + r₂ (v.2 j) + ∑ k, r₂ (v.2 k) * Δ k j
      map_zero' := by ext j; simp
      map_add' := by
        intro v v'
        ext j
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul,
          Finset.sum_add_distrib]
        abel }
  have hT : Continuous T := by
    refine continuous_pi fun j => ?_
    exact ((hr₁.comp ((continuous_apply j).comp continuous_fst)).add
      (hr₂.comp ((continuous_apply j).comp continuous_snd))).add
      (continuous_finsetSum _ fun k _ =>
        (hr₂.comp ((continuous_apply k).comp continuous_snd)).mul continuous_const)
  have happrox : ∀ w : Fin n → A₁₂, ∃ v, ‖v‖ ≤ c * ‖w‖ ∧ ‖w - T v‖ ≤ ‖w‖ / 2 := by
    intro w
    choose h₁ h₂ hh using fun j => hsplit (w j)
    have hb₁ : ∀ j, ‖h₁ j‖ ≤ c * ‖w‖ := fun j =>
      (hh j).2.1.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) hc)
    have hb₂ : ∀ j, ‖h₂ j‖ ≤ c * ‖w‖ := fun j =>
      (hh j).2.2.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) hc)
    have hcw : 0 ≤ c * ‖w‖ := mul_nonneg hc (norm_nonneg _)
    refine ⟨(h₁, h₂), norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg hcw).2 hb₁,
      (pi_norm_le_iff_of_nonneg hcw).2 hb₂⟩, ?_⟩
    have hres : w - T (h₁, h₂) = fun j => -∑ k, r₂ (h₂ k) * Δ k j := by
      ext j
      change w j - (r₁ (h₁ j) + r₂ (h₂ j) + ∑ k, r₂ (h₂ k) * Δ k j) = _
      rw [← (hh j).1]
      abel
    rw [hres]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [norm_neg]
    have hr : ∀ k, ‖r₂ (h₂ k)‖ ≤ L * (c * ‖w‖) := fun k =>
      (hr₂L _).trans (mul_le_mul_of_nonneg_left (hb₂ k) hL)
    calc ‖∑ k, r₂ (h₂ k) * Δ k j‖ ≤ n * (L * (c * ‖w‖) * δ) :=
          norm_sum_mul_le _ _ (mul_nonneg hL hcw) hr fun k => hΔ k j
      _ = n * (L * c * δ) * ‖w‖ := by ring
      _ ≤ 1 / 2 * ‖w‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = ‖w‖ / 2 := by ring
  obtain ⟨v, hv, hvn⟩ := exists_eq_of_approx T hT hc happrox t
  refine ⟨v.1, v.2, fun j => congrFun hv j, fun j => ?_⟩
  exact (norm_le_pi_norm v.1 j).trans ((norm_fst_le v).trans hvn)

end RowSolution

/-- A square matrix whose entries are uniformly small perturbs the identity to a
matrix with a left inverse over a complete normed commutative ring. -/
theorem exists_left_inverse {A : Type*} [NormedCommRing A] [CompleteSpace A] {n : ℕ}
    (P : Fin n → Fin n → A) {η : ℝ} (hP : ∀ k l, ‖P k l‖ ≤ η)
    (hsmall : n * η ≤ 1 / 2) :
    ∃ Q : Fin n → Fin n → A, ∀ i l,
      Q i l + ∑ k, Q i k * P k l = if i = l then 1 else 0 := by
  let T : (Fin n → A) →+ (Fin n → A) :=
    { toFun := fun q l => q l + ∑ k, q k * P k l
      map_zero' := by ext l; simp
      map_add' := by
        intro q q'
        ext l
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        abel }
  have hT : Continuous T := by
    refine continuous_pi fun l => ?_
    exact (continuous_apply l).add (continuous_finsetSum _ fun k _ =>
      (continuous_apply k).mul continuous_const)
  have happrox : ∀ w : Fin n → A, ∃ v, ‖v‖ ≤ 1 * ‖w‖ ∧ ‖w - T v‖ ≤ ‖w‖ / 2 := by
    intro w
    refine ⟨w, by rw [one_mul], ?_⟩
    have hres : w - T w = fun l => -∑ k, w k * P k l := by
      ext l
      change w l - (w l + ∑ k, w k * P k l) = _
      abel
    rw [hres]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
    rw [norm_neg]
    calc ‖∑ k, w k * P k l‖ ≤ n * (‖w‖ * η) :=
          norm_sum_mul_le _ _ (norm_nonneg _) (fun k => norm_le_pi_norm w k) fun k => hP k l
      _ = n * η * ‖w‖ := by ring
      _ ≤ 1 / 2 * ‖w‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = ‖w‖ / 2 := by ring
  choose Q hQ _ using fun i => exists_eq_of_approx T hT zero_le_one happrox
    (fun l => if i = l then (1 : A) else 0)
  exact ⟨Q, fun i l => congrFun (hQ i) l⟩

section Modules

/-- Generators of the source module map to generators of the overlap module. -/
theorem span_image_eq_top {R S M N : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module S N] (r : R → S) (u : M →+ N)
    (hu : ∀ a m, u (a • m) = r a • u m) {n : ℕ} (y : Fin n → M)
    (hy : Submodule.span R (Set.range y) = ⊤) (hspan : Submodule.span S (Set.range u) = ⊤) :
    Submodule.span S (Set.range fun i => u (y i)) = ⊤ := by
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ Submodule.span R (Set.range y) := hy ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hm
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [hu]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Density of the second restriction gives an identity
`u₁ y + Δ u₁ y = u₂ z` with an arbitrarily small matrix `Δ`. -/
theorem exists_small_identity {A₂ A₁₂ M₁ M₂ M₁₂ : Type*} [NormedCommRing A₂]
    [NormedCommRing A₁₂] [AddCommGroup M₁] [AddCommGroup M₂] [Module A₂ M₂]
    [AddCommGroup M₁₂] [Module A₁₂ M₁₂] (r₂ : A₂ → A₁₂) (hdense : DenseRange r₂)
    (u₁ : M₁ →+ M₁₂) (u₂ : M₂ →+ M₁₂) (hu₂ : ∀ a m, u₂ (a • m) = r₂ a • u₂ m)
    {n₁ n₂ : ℕ} (y : Fin n₁ → M₁) (x : Fin n₂ → M₂)
    (D : Fin n₁ → Fin n₂ → A₁₂) (hD : ∀ i, ∑ j, D i j • u₂ (x j) = u₁ (y i))
    (C : Fin n₂ → Fin n₁ → A₁₂) (hC : ∀ j, ∑ l, C j l • u₁ (y l) = u₂ (x j))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (Δ : Fin n₁ → Fin n₁ → A₁₂) (z : Fin n₁ → M₂), (∀ k l, ‖Δ k l‖ ≤ δ) ∧
      ∀ m, u₁ (y m) + ∑ l, Δ m l • u₁ (y l) = u₂ (z m) := by
  set κ : ℝ := ∑ j, ∑ l, ‖C j l‖ + 1 with hκ
  have hκpos : 0 < κ := by
    have : 0 ≤ ∑ j, ∑ l, ‖C j l‖ :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => norm_nonneg _
    linarith
  have hε : 0 < δ / κ := div_pos hδ hκpos
  choose D' hD' using fun i j => hdense.exists_dist_lt (D i j) hε
  refine ⟨fun i l => -∑ j, (D i j - r₂ (D' i j)) * C j l,
    fun i => ∑ j, D' i j • x j, fun i l => ?_, fun m => ?_⟩
  · rw [norm_neg]
    calc ‖∑ j, (D i j - r₂ (D' i j)) * C j l‖
        ≤ ∑ j, ‖(D i j - r₂ (D' i j)) * C j l‖ := norm_sum_le _ _
      _ ≤ ∑ j, δ / κ * ‖C j l‖ := Finset.sum_le_sum fun j _ =>
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (by rw [← dist_eq_norm]; exact (hD' i j).le) (norm_nonneg _))
      _ = δ / κ * ∑ j, ‖C j l‖ := by rw [Finset.mul_sum]
      _ ≤ δ / κ * κ := by
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          have : ∑ j, ‖C j l‖ ≤ ∑ j, ∑ l', ‖C j l'‖ := Finset.sum_le_sum fun j _ =>
            Finset.single_le_sum (f := fun l' => ‖C j l'‖) (fun l' _ => norm_nonneg _)
              (Finset.mem_univ l)
          linarith
      _ = δ := div_mul_cancel₀ δ hκpos.ne'
  · have h1 : ∑ l, (-∑ j, (D m j - r₂ (D' m j)) * C j l) • u₁ (y l) =
        -∑ j, (D m j - r₂ (D' m j)) • u₂ (x j) := by
      simp only [← hC, Finset.smul_sum, smul_smul, neg_smul, Finset.sum_smul,
        Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
    rw [h1, map_sum, ← hD m, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu₂, sub_smul, sub_sub_cancel]

/-- Correcting the small identity by row solutions gives matched families whose
first members generate the first module. -/
theorem exists_matched_generating {A₁ A₂ A₁₂ M₁ M₂ M₁₂ : Type*} [NormedCommRing A₁]
    [NormedCommRing A₂] [NormedCommRing A₁₂] [CompleteSpace A₁] [CompleteSpace A₂]
    [AddCommGroup M₁] [Module A₁ M₁] [AddCommGroup M₂] [Module A₂ M₂]
    [AddCommGroup M₁₂] [Module A₁₂ M₁₂] (r₁ : A₁ →+* A₁₂) (r₂ : A₂ →+* A₁₂)
    (hr₁ : Continuous r₁) (hr₂ : Continuous r₂) {c L δ : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ)
    (hsplit : ∀ h, ∃ h₁ h₂, h = r₁ h₁ + r₂ h₂ ∧ ‖h₁‖ ≤ c * ‖h‖ ∧ ‖h₂‖ ≤ c * ‖h‖)
    (hr₂L : ∀ a, ‖r₂ a‖ ≤ L * ‖a‖)
    (u₁ : M₁ →+ M₁₂) (u₂ : M₂ →+ M₁₂) (hu₁ : ∀ a m, u₁ (a • m) = r₁ a • u₁ m)
    (hu₂ : ∀ a m, u₂ (a • m) = r₂ a • u₂ m)
    {n : ℕ} (y : Fin n → M₁) (hy : Submodule.span A₁ (Set.range y) = ⊤)
    (Δ : Fin n → Fin n → A₁₂) (z : Fin n → M₂) (hΔ : ∀ k l, ‖Δ k l‖ ≤ δ)
    (hI : ∀ m, u₁ (y m) + ∑ l, Δ m l • u₁ (y l) = u₂ (z m))
    (hsmall₁ : n * (L * c * δ) ≤ 1 / 2) (hsmall₂ : n * (c * δ * 2) ≤ 1 / 2) :
    ∃ (w : Fin n → M₁) (w' : Fin n → M₂), (∀ i, u₁ (w i) = u₂ (w' i)) ∧
      Submodule.span A₁ (Set.range w) = ⊤ := by
  choose a b hab ha using fun i =>
    exists_row_solution r₁ r₂ hr₁ hr₂ hc hL hsplit hr₂L Δ hΔ hsmall₁ (fun l => Δ i l)
  have ha' : ∀ i l, ‖a i l‖ ≤ c * δ * 2 := fun i l => (ha i l).trans (by
    have : ‖(fun l => Δ i l)‖ ≤ δ := (pi_norm_le_iff_of_nonneg hδ).2 fun l => hΔ i l
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) (by norm_num))
  obtain ⟨Q, hQ⟩ := exists_left_inverse a ha' hsmall₂
  refine ⟨fun i => y i + ∑ l, a i l • y l, fun i => z i - ∑ k, b i k • z k,
    fun i => ?_, ?_⟩
  · have hr : ∀ l, r₁ (a i l) = Δ i l - r₂ (b i l) - ∑ k, r₂ (b i k) * Δ k l := fun l => by
      rw [← hab i l]; ring
    simp only [map_add, map_sub, map_sum, hu₁, hu₂, hr, ← hI]
    simp only [sub_smul, Finset.sum_sub_distrib, smul_add, Finset.sum_add_distrib,
      Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm (f := fun l k => (r₂ (b i k) * Δ k l) • u₁ (y l))]
    abel
  · have hyw : ∀ i, y i = ∑ k, Q i k • (y k + ∑ l, a k l • y l) := by
      intro i
      have h1 : ∀ l, (Q i l + ∑ k, Q i k * a k l) • y l = if i = l then y l else 0 :=
        fun l => by rw [hQ]; split_ifs <;> simp
      calc y i = ∑ l, (if i = l then y l else 0) := by simp
        _ = ∑ l, (Q i l + ∑ k, Q i k * a k l) • y l := by simp_rw [h1]
        _ = _ := by
          simp only [add_smul, Finset.sum_smul, Finset.sum_add_distrib, smul_add,
            Finset.smul_sum, smul_smul]
          congr 1
          exact Finset.sum_comm
    rw [eq_top_iff, ← hy, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hyw i]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Matched families generating the first module are completed to matched
families generating both modules, using exact splitting of overlap coefficients. -/
theorem exists_matched_generating_both {A₁ A₂ A₁₂ M₁ M₂ M₁₂ : Type*} [CommRing A₁]
    [CommRing A₂] [CommRing A₁₂] [AddCommGroup M₁] [Module A₁ M₁] [AddCommGroup M₂]
    [Module A₂ M₂] [AddCommGroup M₁₂] [Module A₁₂ M₁₂] (r₁ : A₁ → A₁₂) (r₂ : A₂ → A₁₂)
    (hsplit : ∀ h, ∃ h₁ h₂, h = r₁ h₁ + r₂ h₂)
    (u₁ : M₁ →+ M₁₂) (u₂ : M₂ →+ M₁₂) (hu₁ : ∀ a m, u₁ (a • m) = r₁ a • u₁ m)
    (hu₂ : ∀ a m, u₂ (a • m) = r₂ a • u₂ m)
    (hspan₁ : Submodule.span A₁₂ (Set.range u₁) = ⊤)
    {n₁ n₂ : ℕ} (w : Fin n₁ → M₁) (w' : Fin n₁ → M₂) (hw : ∀ i, u₁ (w i) = u₂ (w' i))
    (hwspan : Submodule.span A₁ (Set.range w) = ⊤)
    (x : Fin n₂ → M₂) (hx : Submodule.span A₂ (Set.range x) = ⊤) :
    ∃ (n : ℕ) (X : Fin n → M₁) (Y : Fin n → M₂), (∀ k, u₁ (X k) = u₂ (Y k)) ∧
      Submodule.span A₁ (Set.range X) = ⊤ ∧ Submodule.span A₂ (Set.range Y) = ⊤ := by
  have hw₁₂ := span_image_eq_top r₁ u₁ hu₁ w hwspan hspan₁
  choose e he using fun j => (Submodule.mem_span_range_iff_exists_fun A₁₂).1
    (hw₁₂ ▸ Submodule.mem_top : u₂ (x j) ∈ Submodule.span A₁₂ (Set.range fun k => u₁ (w k)))
  choose α β hαβ using fun j k => hsplit (e j k)
  refine ⟨n₁ + n₂, Fin.append w fun j => ∑ k, α j k • w k,
    Fin.append w' fun j => x j - ∑ k, β j k • w' k, fun k => ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, hw]
    · simp only [Fin.append_right]
      rw [map_sum, map_sub, map_sum, ← he j]
      simp only [hu₁, hu₂, ← hw]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← sub_smul, hαβ j k, add_sub_cancel_right]
  · rw [eq_top_iff, ← hwspan]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd n₂ i, Fin.append_left _ _ i⟩
  · rw [eq_top_iff, ← hx, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hxj : x j = Fin.append w' (fun j => x j - ∑ k, β j k • w' k) (Fin.natAdd n₁ j) +
        ∑ k, β j k • Fin.append w' (fun j => x j - ∑ k, β j k • w' k) (Fin.castAdd n₂ k) := by
      simp only [Fin.append_left, Fin.append_right, sub_add_cancel]
    rw [hxj]
    exact add_mem (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

/-- A positive radius making both smallness conditions hold. -/
theorem exists_small_constant (n : ℕ) {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c) :
    ∃ δ : ℝ, 0 < δ ∧ n * (L * c * δ) ≤ 1 / 2 ∧ n * (c * δ * 2) ≤ 1 / 2 := by
  have hLc : 0 ≤ L * c := mul_nonneg hL hc
  set B : ℝ := L * c + c + 1 with hBdef
  have hB : 0 < B := by linarith
  have hN : (0 : ℝ) < n + 1 := by positivity
  refine ⟨1 / (4 * ((n : ℝ) + 1) * B), by positivity, ?_, ?_⟩
  · have hNBδ : ((n : ℝ) + 1) * (B * (1 / (4 * ((n : ℝ) + 1) * B))) = 1 / 4 := by
      field_simp
    calc (n : ℝ) * (L * c * (1 / (4 * ((n : ℝ) + 1) * B)))
        ≤ ((n : ℝ) + 1) * (B * (1 / (4 * ((n : ℝ) + 1) * B))) := by
          apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right (by linarith)
            (by positivity)) (by positivity) (by positivity)
      _ ≤ 1 / 2 := by rw [hNBδ]; norm_num
  · have hNBδ : ((n : ℝ) + 1) * (B * (1 / (4 * ((n : ℝ) + 1) * B)) * 2) = 1 / 2 := by
      field_simp
      ring
    calc (n : ℝ) * (c * (1 / (4 * ((n : ℝ) + 1) * B)) * 2)
        ≤ ((n : ℝ) + 1) * (B * (1 / (4 * ((n : ℝ) + 1) * B)) * 2) := by
          apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by norm_num))
            (by positivity) (by positivity)
      _ = 1 / 2 := hNBδ

end Modules

end Langlands.Analytic.BoundedAlgHom.SplitSquareGeneration

namespace Langlands.Analytic.BoundedAlgHom

open SplitSquareGeneration in
/-- Matched generation of finite modules over a split square. -/
theorem splitSquareModuleGeneration : SplitSquareModuleGenerationStatement.{u, v, w} := by
  intro K _ A A₁ A₂ A₁₂ _ _ _ _ _ _ _ _ _ _ p₁ p₂ r₁ r₂ hS M₁ M₂ M₁₂ _ _ _ _ _ _ u₁ u₂
    hu₁ hu₂ hM₁ hM₂ hspan₁ hspan₂
  obtain ⟨S⟩ := hS
  obtain ⟨n₁, y, hy⟩ := @Module.Finite.exists_fin A₁ M₁ _ _ _ hM₁
  obtain ⟨n₂, x, hx⟩ := @Module.Finite.exists_fin A₂ M₂ _ _ _ hM₂
  let ρ₁ : A₁ →+* A₁₂ := r₁.toAlgHom.toRingHom
  let ρ₂ : A₂ →+* A₁₂ := r₂.toAlgHom.toRingHom
  obtain ⟨L₁, _, hb₁⟩ := r₁.bounded
  obtain ⟨L, hL, hb₂⟩ := r₂.bounded
  have hc₁ : Continuous ρ₁ := AddMonoidHomClass.continuous_of_bound ρ₁ L₁ hb₁
  have hc₂ : Continuous ρ₂ := AddMonoidHomClass.continuous_of_bound ρ₂ L hb₂
  have hy₁₂ := span_image_eq_top r₁ u₁ hu₁ y hy hspan₁
  have hx₁₂ := span_image_eq_top r₂ u₂ hu₂ x hx hspan₂
  choose D hD using fun i => (Submodule.mem_span_range_iff_exists_fun A₁₂).1
    (hx₁₂ ▸ Submodule.mem_top : u₁ (y i) ∈ Submodule.span A₁₂ (Set.range fun j => u₂ (x j)))
  choose C hC using fun j => (Submodule.mem_span_range_iff_exists_fun A₁₂).1
    (hy₁₂ ▸ Submodule.mem_top : u₂ (x j) ∈ Submodule.span A₁₂ (Set.range fun l => u₁ (y l)))
  obtain ⟨δ, hδ, hsmall₁, hsmall₂⟩ := exists_small_constant n₁ hL.le S.bound_nonneg
  obtain ⟨Δ, z, hΔ, hI⟩ := exists_small_identity r₂ S.dense u₁ u₂ hu₂ y x D hD C hC hδ
  obtain ⟨w, w', hw, hwspan⟩ := exists_matched_generating ρ₁ ρ₂ hc₁ hc₂ S.bound_nonneg hL.le
    hδ.le S.split hb₂ u₁ u₂ hu₁ hu₂ y hy Δ z hΔ hI hsmall₁ hsmall₂
  exact exists_matched_generating_both r₁ r₂
    (fun h => let ⟨h₁, h₂, he, _⟩ := S.split h; ⟨h₁, h₂, he⟩) u₁ u₂ hu₁ hu₂ hspan₁ w w' hw
    hwspan x hx

end Langlands.Analytic.BoundedAlgHom
