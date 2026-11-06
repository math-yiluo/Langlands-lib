import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescent

/-! # Closed-ideal effectiveness for a split square of bounded algebra maps -/

noncomputable section

universe u v w x y z

namespace Langlands.Analytic.BoundedAlgHom

open Filter Topology

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {A₁ : Type w} [NormedCommRing A₁] [NormedAlgebra K A₁]
  {A₂ : Type x} [NormedCommRing A₂] [NormedAlgebra K A₂]
  {A₁₂ : Type y} [NormedCommRing A₁₂] [NormedAlgebra K A₁₂]

/-- A split square of bounded algebra maps: the square `r₁ ∘ p₁ = r₂ ∘ p₂`
commutes, compatible pairs of elements glue to an element of `A`, the second
restriction has dense range, and every overlap element splits as
`r₁ h₁ + r₂ h₂` with both norms bounded by `bound` times its norm. -/
structure SplitSquare (p₁ : BoundedAlgHom K A A₁) (p₂ : BoundedAlgHom K A A₂)
    (r₁ : BoundedAlgHom K A₁ A₁₂) (r₂ : BoundedAlgHom K A₂ A₁₂) where
  comm : ∀ a, r₁ (p₁ a) = r₂ (p₂ a)
  glue : ∀ a₁ a₂, r₁ a₁ = r₂ a₂ → ∃ a, p₁ a = a₁ ∧ p₂ a = a₂
  dense : DenseRange r₂
  /-- The splitting constant. -/
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  split : ∀ h, ∃ h₁ h₂, h = r₁ h₁ + r₂ h₂ ∧ ‖h₁‖ ≤ bound * ‖h‖ ∧ ‖h₂‖ ≤ bound * ‖h‖

namespace SplitSquare

variable (r₁ : BoundedAlgHom K A₁ A₁₂) (r₂ : BoundedAlgHom K A₂ A₁₂)

/-- Approximate splittings into closed ideals whose remainders halve in size
give exact splittings. -/
theorem exists_split_of_approx [CompleteSpace A₁] [CompleteSpace A₂]
    {V : Type z} (N : V → ℝ) (Φ : V → A₁₂) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hΦ : ∀ v, ‖Φ v‖ ≤ M * N v) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    (hI₁ : IsClosed (I₁ : Set A₁)) (hI₂ : IsClosed (I₂ : Set A₂))
    (step : ∀ v, ∃ e₁ ∈ I₁, ∃ e₂ ∈ I₂, ∃ v', Φ v = r₁ e₁ + r₂ e₂ + Φ v' ∧
      ‖e₁‖ ≤ c * N v ∧ ‖e₂‖ ≤ c * N v ∧ N v' ≤ N v / 2) (v : V) :
    ∃ e₁ ∈ I₁, ∃ e₂ ∈ I₂, Φ v = r₁ e₁ + r₂ e₂ ∧ ‖e₁‖ ≤ 2 * c * N v := by
  choose E₁ hE₁ E₂ hE₂ W hW using step
  let s : ℕ → V := fun k => W^[k] v
  have hs_succ (k : ℕ) : s (k + 1) = W (s k) := Function.iterate_succ_apply' W k v
  have hN (k : ℕ) : N (s k) ≤ N v / 2 ^ k := by
    induction k with
    | zero => simp [s]
    | succ k ih =>
      rw [hs_succ]
      calc N (W (s k)) ≤ N (s k) / 2 := (hW (s k)).2.2.2
        _ ≤ N v / 2 ^ k / 2 := by gcongr
        _ = N v / 2 ^ (k + 1) := by rw [pow_succ, div_div]
  have hbound (k : ℕ) : c * N (s k) ≤ 2 * c * N v / 2 / 2 ^ k := by
    calc c * N (s k) ≤ c * (N v / 2 ^ k) := mul_le_mul_of_nonneg_left (hN k) hc
      _ = 2 * c * N v / 2 / 2 ^ k := by ring
  have hg := hasSum_geometric_two' (2 * c * N v)
  have h₁b (k : ℕ) : ‖E₁ (s k)‖ ≤ 2 * c * N v / 2 / 2 ^ k :=
    ((hW (s k)).2.1).trans (hbound k)
  have h₂b (k : ℕ) : ‖E₂ (s k)‖ ≤ 2 * c * N v / 2 / 2 ^ k :=
    ((hW (s k)).2.2.1).trans (hbound k)
  have hs₁ : Summable fun k => E₁ (s k) := Summable.of_norm_bounded hg.summable h₁b
  have hs₂ : Summable fun k => E₂ (s k) := Summable.of_norm_bounded hg.summable h₂b
  have ht₁ := hs₁.hasSum.tendsto_sum_nat
  have ht₂ := hs₂.hasSum.tendsto_sum_nat
  have hpartial (n : ℕ) : Φ v = r₁ (∑ i ∈ Finset.range n, E₁ (s i)) +
      r₂ (∑ i ∈ Finset.range n, E₂ (s i)) + Φ (s n) := by
    induction n with
    | zero => simp [s]
    | succ n ih =>
      rw [ih, (hW (s n)).1, Finset.sum_range_succ, Finset.sum_range_succ, map_add, map_add,
        hs_succ]
      abel
  have hrem : Tendsto (fun n => Φ (s n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => (hΦ (s n)).trans
      (mul_le_mul_of_nonneg_left (hN n) hM))
    have h2 : Tendsto (fun n : ℕ => N v / 2 ^ n) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, ← inv_pow, mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num)).const_mul (N v)
    simpa using h2.const_mul M
  have hlim : Tendsto (fun n => r₁ (∑ i ∈ Finset.range n, E₁ (s i)) +
      r₂ (∑ i ∈ Finset.range n, E₂ (s i)) + Φ (s n)) atTop
      (𝓝 (r₁ (∑' k, E₁ (s k)) + r₂ (∑' k, E₂ (s k)) + 0)) :=
    (((r₁.continuous.tendsto _).comp ht₁).add ((r₂.continuous.tendsto _).comp ht₂)).add hrem
  simp_rw [← hpartial] at hlim
  refine ⟨∑' k, E₁ (s k), ?_, ∑' k, E₂ (s k), ?_, ?_, ?_⟩
  · exact hI₁.mem_of_tendsto ht₁ (Eventually.of_forall fun n =>
      Ideal.sum_mem _ fun i _ => hE₁ (s i))
  · exact hI₂.mem_of_tendsto ht₂ (Eventually.of_forall fun n =>
      Ideal.sum_mem _ fun i _ => hE₂ (s i))
  · rw [← add_zero (r₁ _ + _)]
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  · exact tsum_of_norm_bounded hg h₁b


/-- One approximate splitting step for ideals with chosen generators on both
sides. -/
theorem exists_split_of_generators [CompleteSpace A₁] [CompleteSpace A₂]
    {n m : ℕ} {I₁ : Ideal A₁} {I₂ : Ideal A₂}
    (hI₁ : IsClosed (I₁ : Set A₁)) (hI₂ : IsClosed (I₂ : Set A₂))
    (x : Fin n → A₁) (y : Fin m → A₂) (hx : ∀ k, x k ∈ I₁) (hy : ∀ l, y l ∈ I₂)
    (B : Fin n → Fin m → A₁₂) (hB : ∀ k, ∑ l, B k l * r₂ (y l) = r₁ (x k))
    (C : Fin m → Fin n → A₁₂) (hC : ∀ l, ∑ k, C l k * r₁ (x k) = r₂ (y l))
    (hdense : DenseRange r₂) {β : ℝ} (hβ : 0 ≤ β)
    (hsplit : ∀ h, ∃ h₁ h₂, h = r₁ h₁ + r₂ h₂ ∧ ‖h₁‖ ≤ β * ‖h‖ ∧ ‖h₂‖ ≤ β * ‖h‖) :
    ∃ c, 0 ≤ c ∧ ∀ u : Fin n → A₁₂, ∃ e₁ ∈ I₁, ∃ e₂ ∈ I₂,
      ∑ k, u k * r₁ (x k) = r₁ e₁ + r₂ e₂ ∧ ‖e₁‖ ≤ c * ∑ k, ‖u k‖ := by
  obtain ⟨R, hR, hr₂⟩ := r₂.bounded
  have hMC : 0 ≤ ∑ l, ∑ j, ‖C l j‖ := by positivity
  set δ : ℝ := 1 / (2 * (R * β * ∑ l, ∑ j, ‖C l j‖ + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ2 : R * β * δ * ∑ l, ∑ j, ‖C l j‖ ≤ 1 / 2 := by
    have h0 : 0 ≤ R * β * ∑ l, ∑ j, ‖C l j‖ := by positivity
    rw [hδ, div_eq_mul_inv, one_mul]
    rw [show R * β * (2 * (R * β * ∑ l, ∑ j, ‖C l j‖ + 1))⁻¹ * ∑ l, ∑ j, ‖C l j‖ =
      (R * β * ∑ l, ∑ j, ‖C l j‖) / (2 * (R * β * ∑ l, ∑ j, ‖C l j‖ + 1)) by ring]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hBapprox : ∀ k l, ∃ b, ‖B k l - r₂ b‖ < δ := fun k l => by
    obtain ⟨b, hb⟩ := Metric.denseRange_iff.mp hdense (B k l) δ hδ0
    exact ⟨b, by rw [← dist_eq_norm]; exact hb⟩
  choose B' hB' using hBapprox
  choose S₁ S₂ hS using hsplit
  set c : ℝ := β * (∑ k, ‖x k‖ + ∑ k, ∑ l, ‖B' k l‖ * ‖y l‖) with hc
  have hc0 : 0 ≤ c := by positivity
  have hΦ (v : Fin n → A₁₂) :
      ‖∑ k, v k * r₁ (x k)‖ ≤ (∑ k, ‖r₁ (x k)‖) * ∑ k, ‖v k‖ := by
    calc ‖∑ k, v k * r₁ (x k)‖ ≤ ∑ k, ‖v k‖ * ‖r₁ (x k)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
      _ ≤ ∑ k, (∑ k, ‖v k‖) * ‖r₁ (x k)‖ := by
          gcongr with k
          exact Finset.single_le_sum (f := fun k => ‖v k‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ k)
      _ = (∑ k, ‖r₁ (x k)‖) * ∑ k, ‖v k‖ := by rw [← Finset.mul_sum, mul_comm]
  refine ⟨2 * c, by positivity, fun u => ?_⟩
  suffices step : ∀ v : Fin n → A₁₂, ∃ e₁ ∈ I₁, ∃ e₂ ∈ I₂, ∃ v' : Fin n → A₁₂,
      ∑ k, v k * r₁ (x k) = r₁ e₁ + r₂ e₂ + ∑ k, v' k * r₁ (x k) ∧
      ‖e₁‖ ≤ c * ∑ k, ‖v k‖ ∧ ‖e₂‖ ≤ c * ∑ k, ‖v k‖ ∧
      ∑ k, ‖v' k‖ ≤ (∑ k, ‖v k‖) / 2 by
    exact exists_split_of_approx r₁ r₂
      (fun u : Fin n → A₁₂ => ∑ k, ‖u k‖) (fun u => ∑ k, u k * r₁ (x k))
      (by positivity) hc0 hΦ I₁ I₂ hI₁ hI₂ step u
  intro v
  set p : Fin n → A₁ := fun k => S₁ (v k)
  set q : Fin n → A₂ := fun k => S₂ (v k)
  set D : Fin n → Fin m → A₁₂ := fun k l => B k l - r₂ (B' k l)
  have hv (k : Fin n) : v k = r₁ (p k) + r₂ (q k) := (hS (v k)).1
  have hp (k : Fin n) : ‖p k‖ ≤ β * ‖v k‖ := (hS (v k)).2.1
  have hq (k : Fin n) : ‖q k‖ ≤ β * ‖v k‖ := (hS (v k)).2.2
  have hN (k : Fin n) : ‖v k‖ ≤ ∑ k, ‖v k‖ :=
    Finset.single_le_sum (f := fun k => ‖v k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  refine ⟨∑ k, p k * x k, Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hx k),
    ∑ k, ∑ l, q k * B' k l * y l,
    Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hy l),
    fun j => ∑ k, ∑ l, r₂ (q k) * D k l * C l j, ?_, ?_, ?_, ?_⟩
  · have h1 (k : Fin n) : v k * r₁ (x k) = r₁ (p k * x k) +
        r₂ (∑ l, q k * B' k l * y l) + ∑ l, ∑ j, r₂ (q k) * D k l * C l j * r₁ (x j) := by
      rw [hv k, add_mul, ← map_mul, ← hB k, Finset.mul_sum, map_sum, add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      have hsum : ∑ j, r₂ (q k) * D k l * C l j * r₁ (x j) =
          r₂ (q k) * D k l * r₂ (y l) := by
        rw [← hC l, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum]
      simp only [D, map_mul]
      ring
    rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← map_sum, ← map_sum]
    congr 1
    simp only [Finset.sum_mul]
    exact (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans Finset.sum_comm
  · have hN0 : 0 ≤ ∑ k, ‖v k‖ := by positivity
    have hY : 0 ≤ ∑ k, ∑ l, ‖B' k l‖ * ‖y l‖ := by positivity
    calc ‖∑ k, p k * x k‖ ≤ ∑ k, ‖p k‖ * ‖x k‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
      _ ≤ ∑ k, (β * ∑ k, ‖v k‖) * ‖x k‖ := by
          gcongr with k
          exact (hp k).trans (mul_le_mul_of_nonneg_left (hN k) hβ)
      _ = β * (∑ k, ‖x k‖) * ∑ k, ‖v k‖ := by rw [← Finset.mul_sum]; ring
      _ ≤ c * ∑ k, ‖v k‖ := by
          rw [hc]
          gcongr
          linarith
  · have hN0 : 0 ≤ ∑ k, ‖v k‖ := by positivity
    have hX : 0 ≤ ∑ k, ‖x k‖ := by positivity
    calc ‖∑ k, ∑ l, q k * B' k l * y l‖ ≤ ∑ k, ∑ l, ‖q k‖ * ‖B' k l‖ * ‖y l‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun l _ => (norm_mul_le _ _).trans
              (by gcongr; exact norm_mul_le _ _)))
      _ ≤ ∑ k, ∑ l, (β * ∑ k, ‖v k‖) * ‖B' k l‖ * ‖y l‖ := by
          gcongr with k l
          exact (hq k).trans (mul_le_mul_of_nonneg_left (hN k) hβ)
      _ = β * (∑ k, ∑ l, ‖B' k l‖ * ‖y l‖) * ∑ k, ‖v k‖ := by
          generalize ∑ k, ‖v k‖ = N
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      _ ≤ c * ∑ k, ‖v k‖ := by
          rw [hc]
          gcongr
          linarith
  · have hN0 : 0 ≤ ∑ k, ‖v k‖ := by positivity
    calc ∑ j, ‖∑ k, ∑ l, r₂ (q k) * D k l * C l j‖
        ≤ ∑ j, ∑ k, ∑ l, R * β * δ * (‖v k‖ * ‖C l j‖) := by
          refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun l _ => ?_))
          calc ‖r₂ (q k) * D k l * C l j‖ ≤ ‖r₂ (q k)‖ * ‖D k l‖ * ‖C l j‖ :=
                (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
            _ ≤ (R * (β * ‖v k‖)) * δ * ‖C l j‖ := by
                gcongr
                · exact (hr₂ (q k)).trans (mul_le_mul_of_nonneg_left (hq k) hR.le)
                · exact (hB' k l).le
            _ = R * β * δ * (‖v k‖ * ‖C l j‖) := by ring
      _ = R * β * δ * (∑ l, ∑ j, ‖C l j‖) * ∑ k, ‖v k‖ := by
          rw [Finset.sum_comm, mul_comm _ (∑ k, ‖v k‖), Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm, mul_comm, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 1 / 2 * ∑ k, ‖v k‖ := by gcongr
      _ = (∑ k, ‖v k‖) / 2 := by ring

variable {r₁ r₂}

/-- Closed-ideal effectiveness for a split square: if `A₁` and `A₂` are complete
and Noetherian and all ideals of `A₁`, `A₂` and `A₁₂` are closed, then ideals
with equal closed extensions to the overlap are the closed extensions of the
ideal of global elements lying in both of them. -/
theorem closedIdealMap_inf_comap_eq [CompleteSpace A₁] [CompleteSpace A₂]
    [IsNoetherianRing A₁] [IsNoetherianRing A₂]
    {p₁ : BoundedAlgHom K A A₁} {p₂ : BoundedAlgHom K A A₂} (S : SplitSquare p₁ p₂ r₁ r₂)
    (hA₁ : ∀ I : Ideal A₁, IsClosed (I : Set A₁))
    (hA₂ : ∀ I : Ideal A₂, IsClosed (I : Set A₂))
    (hA₁₂ : ∀ I : Ideal A₁₂, IsClosed (I : Set A₁₂))
    (I₁ : Ideal A₁) (I₂ : Ideal A₂) (hI : r₁.closedIdealMap I₁ = r₂.closedIdealMap I₂) :
    p₁.closedIdealMap (I₁.comap p₁.toAlgHom.toRingHom ⊓ I₂.comap p₂.toAlgHom.toRingHom) = I₁ ∧
      p₂.closedIdealMap (I₁.comap p₁.toAlgHom.toRingHom ⊓ I₂.comap p₂.toAlgHom.toRingHom) =
        I₂ := by
  obtain ⟨hcomm, hglue, hdense, β, hβ, hsplit⟩ := S
  set J := I₁.comap p₁.toAlgHom.toRingHom ⊓ I₂.comap p₂.toAlgHom.toRingHom with hJ
  have hI' : Ideal.map r₁.toAlgHom.toRingHom I₁ = Ideal.map r₂.toAlgHom.toRingHom I₂ := by
    have h₁ := IsClosed.submodule_topologicalClosure_eq (hA₁₂ (Ideal.map r₁.toAlgHom.toRingHom I₁))
    have h₂ := IsClosed.submodule_topologicalClosure_eq (hA₁₂ (Ideal.map r₂.toAlgHom.toRingHom I₂))
    rw [← h₁, ← h₂]
    exact hI
  obtain ⟨n, x, hxspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I₁)
  obtain ⟨m, y, hyspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I₂)
  have hxspan' : Ideal.span (Set.range x) = I₁ := hxspan
  have hyspan' : Ideal.span (Set.range y) = I₂ := hyspan
  have hx (k : Fin n) : x k ∈ I₁ := hxspan' ▸ Ideal.subset_span ⟨k, rfl⟩
  have hy (l : Fin m) : y l ∈ I₂ := hyspan' ▸ Ideal.subset_span ⟨l, rfl⟩
  have hmapx : Ideal.map r₁.toAlgHom.toRingHom I₁ = Ideal.span (Set.range fun k => r₁ (x k)) := by
    rw [← hxspan', Ideal.map_span, ← Set.range_comp]
    rfl
  have hmapy : Ideal.map r₂.toAlgHom.toRingHom I₂ = Ideal.span (Set.range fun l => r₂ (y l)) := by
    rw [← hyspan', Ideal.map_span, ← Set.range_comp]
    rfl
  have hB (k : Fin n) : ∃ b : Fin m → A₁₂, ∑ l, b l * r₂ (y l) = r₁ (x k) := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← hmapy, ← hI']
    exact Ideal.mem_map_of_mem _ (hx k)
  have hC (l : Fin m) : ∃ b : Fin n → A₁₂, ∑ k, b k * r₁ (x k) = r₂ (y l) := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← hmapx, hI']
    exact Ideal.mem_map_of_mem _ (hy l)
  choose B hB using hB
  choose C hC using hC
  have hJ₁ : Ideal.map p₁.toAlgHom.toRingHom J ≤ I₁ :=
    Ideal.map_le_iff_le_comap.mpr inf_le_left
  have hJ₂ : Ideal.map p₂.toAlgHom.toRingHom J ≤ I₂ :=
    Ideal.map_le_iff_le_comap.mpr inf_le_right
  -- The first side: approximate global representatives via density.
  have side₁ : p₁.closedIdealMap J = I₁ := by
    refine le_antisymm ((p₁.closedIdealMap_le_iff _ _ (hA₁ I₁)).mpr inf_le_left) ?_
    obtain ⟨c, hc0, hstep⟩ := exists_split_of_generators r₁ r₂ (hA₁ I₁) (hA₂ I₂) x y hx hy
      B hB C hC hdense hβ hsplit
    intro g hg
    obtain ⟨c', hc'⟩ : ∃ c' : Fin m → A₁₂, ∑ l, c' l * r₂ (y l) = r₁ g := by
      apply Ideal.mem_span_range_iff_exists_fun.mp
      rw [← hmapy, ← hI']
      exact Ideal.mem_map_of_mem _ hg
    change g ∈ ((Ideal.map p₁.toAlgHom.toRingHom J).topologicalClosure : Set A₁)
    rw [Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
    intro ε hε
    have hMC : 0 ≤ ∑ k, ∑ l, ‖C l k‖ := by positivity
    set η : ℝ := ε / (c * ∑ k, ∑ l, ‖C l k‖ + 1) with hη
    have hη0 : 0 < η := by positivity
    have hd (l : Fin m) : ∃ d, ‖c' l - r₂ d‖ < η := by
      obtain ⟨d, hd⟩ := Metric.denseRange_iff.mp hdense (c' l) η hη0
      exact ⟨d, by rw [← dist_eq_norm]; exact hd⟩
    choose d hd using hd
    obtain ⟨e₁, he₁, e₂, he₂, heq, hle⟩ :=
      hstep fun k => ∑ l, (c' l - r₂ (d l)) * C l k
    have hsum : ∑ k, (∑ l, (c' l - r₂ (d l)) * C l k) * r₁ (x k) =
        r₁ g - r₂ (∑ l, d l * y l) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm, ← hc', map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, ← hC l, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum] at heq
    obtain ⟨a, ha₁, ha₂⟩ := hglue (g - e₁) (∑ l, d l * y l + e₂) (by
      rw [map_sub, map_add]
      linear_combination heq)
    have haJ : a ∈ J := by
      refine ⟨?_, ?_⟩
      · change p₁ a ∈ I₁
        rw [ha₁]
        exact I₁.sub_mem hg he₁
      · change p₂ a ∈ I₂
        rw [ha₂]
        exact I₂.add_mem (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hy l)) he₂
    refine ⟨g - e₁, ?_, ?_⟩
    · rw [← ha₁]
      exact Ideal.mem_map_of_mem _ haJ
    · rw [dist_eq_norm, sub_sub_cancel]
      have hu : ∑ k, ‖∑ l, (c' l - r₂ (d l)) * C l k‖ ≤ η * ∑ k, ∑ l, ‖C l k‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun l _ => (norm_mul_le _ _).trans ?_
        gcongr
        exact (hd l).le
      calc ‖e₁‖ ≤ c * ∑ k, ‖∑ l, (c' l - r₂ (d l)) * C l k‖ := hle
        _ ≤ c * (η * ∑ k, ∑ l, ‖C l k‖) := by gcongr
        _ = ε * (c * ∑ k, ∑ l, ‖C l k‖) / (c * ∑ k, ∑ l, ‖C l k‖ + 1) := by
          rw [hη]
          ring
        _ < ε := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [mul_nonneg hc0 hMC]
  refine ⟨side₁, ?_⟩
  -- The second side: exact splitting and gluing.
  refine le_antisymm ((p₂.closedIdealMap_le_iff _ _ (hA₂ I₂)).mpr inf_le_right) ?_
  have hJclosed : Ideal.map p₁.toAlgHom.toRingHom J = I₁ := by
    rw [← side₁]
    exact (IsClosed.submodule_topologicalClosure_eq (hA₁ _)).symm
  intro h hh
  have hmem : r₂ h ∈ Ideal.map (r₁.toAlgHom.toRingHom.comp p₁.toAlgHom.toRingHom) J := by
    rw [← Ideal.map_map, hJclosed, hI']
    exact Ideal.mem_map_of_mem _ hh
  have key : ∀ d : A₁₂, ∃ t ∈ I₁, ∃ s ∈ Ideal.map p₂.toAlgHom.toRingHom J,
      d * r₂ h = r₁ t + r₂ s := by
    refine Submodule.span_induction
      (p := fun z _ => ∀ d : A₁₂, ∃ t ∈ I₁, ∃ s ∈ Ideal.map p₂.toAlgHom.toRingHom J,
        d * z = r₁ t + r₂ s) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨j, hj, rfl⟩ d
      obtain ⟨d₁, d₂, hd, -⟩ := hsplit d
      refine ⟨d₁ * p₁ j, Ideal.mul_mem_left _ _ hj.1, d₂ * p₂ j,
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hj), ?_⟩
      change d * r₁ (p₁ j) = _
      rw [hd, map_mul, map_mul, hcomm]
      ring
    · intro d
      exact ⟨0, I₁.zero_mem, 0, Submodule.zero_mem _, by simp⟩
    · intro z w _ _ hz hw d
      obtain ⟨t, ht, s, hs, hts⟩ := hz d
      obtain ⟨t', ht', s', hs', hts'⟩ := hw d
      exact ⟨t + t', I₁.add_mem ht ht', s + s', Submodule.add_mem _ hs hs', by
        rw [mul_add, hts, hts', map_add, map_add]
        abel⟩
    · intro b z _ hz d
      obtain ⟨t, ht, s, hs, hts⟩ := hz (d * b)
      exact ⟨t, ht, s, hs, by rw [smul_eq_mul, ← mul_assoc, hts]⟩
  obtain ⟨t, ht, s, hs, hts⟩ := key 1
  rw [one_mul] at hts
  obtain ⟨a, ha₁, ha₂⟩ := hglue (-t) (s - h) (by
    rw [map_neg, map_sub]
    linear_combination hts)
  have haJ : a ∈ J := by
    refine ⟨?_, ?_⟩
    · change p₁ a ∈ I₁
      rw [ha₁]
      exact I₁.neg_mem ht
    · change p₂ a ∈ I₂
      rw [ha₂]
      exact I₂.sub_mem (hJ₂ hs) hh
  have : h = s - p₂ a := by rw [ha₂]; abel
  rw [this]
  exact p₂.closedIdealMap J |>.sub_mem
    ((Ideal.map p₂.toAlgHom.toRingHom J).le_topologicalClosure hs)
    (p₂.mem_closedIdealMap haJ)

end SplitSquare

end Langlands.Analytic.BoundedAlgHom
