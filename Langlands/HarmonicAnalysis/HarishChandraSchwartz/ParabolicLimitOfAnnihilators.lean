import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermUniqueness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.PositivePartDecay

/-!
# Parabolic limits from annihilators at strict points

An abstract criterion for `TendstoZeroAlongParabolic`: a function on a commutative group which
is annihilated, at every strict point `y` of a subgroup, by a monic polynomial in the right
translation by `y` with roots of modulus `< 1`, and which is bounded on the deep shells
`R₀ < α(H(a)) ≤ B`, tends to `0` along the parabolic.
-/

open Filter Polynomial Topology Langlands.HarmonicAnalysis

namespace Langlands.HarishChandraSchwartz

section Halving

variable {G : Type*} [Group G]

/-- **Halving decay along `z`**: whenever `‖φ(b zᵉ)‖ ≤ C` for `e < N`, one has
`‖φ(b zⁿ)‖ ≤ C 2^N 2^{-n}` for every `n`. -/
def HasHalvingDecay (φ : G → ℂ) (z : G) (N : ℕ) : Prop :=
  ∀ (b : G) (C : ℝ), 0 ≤ C → (∀ e < N, ‖φ (b * z ^ e)‖ ≤ C) →
    ∀ n : ℕ, ‖φ (b * z ^ n)‖ ≤ C * 2 ^ N * (1 / 2) ^ n

/-- `1 ≤ 2^N 2^{-n}` for `n ≤ N`. -/
theorem one_le_two_pow_mul_half_pow {N n : ℕ} (h : n ≤ N) :
    (1 : ℝ) ≤ 2 ^ N * (1 / 2) ^ n := by
  have e : (2 : ℝ) ^ N = 2 ^ (N - n) * 2 ^ n := by
    rw [← pow_add]
    congr 1
    omega
  rw [e, mul_assoc, ← mul_pow]
  norm_num
  exact one_le_pow₀ (by norm_num)

/-- **One direction.** If a monic `P` with roots of modulus at most `θ < 1` kills `φ` under the
right translation by `y`, then for all large `q` the function `φ` has halving decay along `y^q`
with `N = deg P`. -/
theorem exists_hasHalvingDecay_pow {φ : G → ℂ} {y : G} {P : ℂ[X]} (hP : P.Monic) {θ : ℝ}
    (hθ : θ < 1) (hroots : ∀ z ∈ P.roots, ‖z‖ ≤ θ)
    (h : aeval (GroupAction.rightFunctions y) P φ = 0) :
    ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → HasHalvingDecay φ (y ^ q) P.natDegree := by
  set θ' : ℝ := max θ 0 with hθ'
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθ'1 : θ' < 1 := max_lt hθ (by norm_num)
  have hroots' : ∀ z ∈ P.roots, ‖z‖ ≤ θ' := fun z hz => (hroots z hz).trans (le_max_left _ _)
  obtain ⟨q₀, -, hq₀⟩ := exists_pow_coeff_small P.natDegree hθ'0 hθ'1
  refine ⟨q₀, fun q hq b C hC h0 n => ?_⟩
  have hann : aeval (GroupAction.rightFunctions (y ^ q)) (rootPowerPolynomial P q) φ = 0 := by
    rw [map_pow]
    exact aeval_rootPowerPolynomial_eq_zero _ hP q h
  have hc : ∀ k < (rootPowerPolynomial P q).natDegree,
      ‖(rootPowerPolynomial P q).coeff k‖ ≤
        (1 / 2) ^ ((rootPowerPolynomial P q).natDegree - k) /
          (rootPowerPolynomial P q).natDegree := by
    intro k hk
    rw [natDegree_rootPowerPolynomial] at hk ⊢
    refine (norm_coeff_rootPowerPolynomial_le hθ'0 hroots' q hk.le).trans
      (le_trans ?_ (hq₀ (P.natDegree - k) (by omega) (by omega)))
    have hpow : θ' ^ q ≤ θ' ^ q₀ := pow_le_pow_of_le_one hθ'0 hθ'1.le hq
    gcongr
  have hK : 0 ≤ C * 2 ^ P.natDegree := by positivity
  refine norm_le_of_aeval_eq_zero (y ^ q) (rootPowerPolynomial_monic P q) hc hann b hK
    (fun e he => ?_) n
  rw [natDegree_rootPowerPolynomial] at he
  calc ‖φ (b * (y ^ q) ^ e)‖ ≤ C := h0 e he
    _ = C * 1 := (mul_one C).symm
    _ ≤ C * (2 ^ P.natDegree * (1 / 2) ^ e) :=
        mul_le_mul_of_nonneg_left (one_le_two_pow_mul_half_pow he.le) hC
    _ = C * 2 ^ P.natDegree * (1 / 2) ^ e := by ring

end Halving

section MultiDirection

variable {G : Type*} [CommGroup G]

/-- **Several directions.** If `φ` has halving decay along each `z i`, `i ∈ s`, and
`‖φ(a ∏ z_i^{e_i})‖ ≤ C` whenever `e_i < N_i` for all `i ∈ s`, then
`‖φ(a ∏ z_i^{n_i})‖ ≤ C ∏ 2^{N_i} 2^{-∑ n_i}` for every `n`. -/
theorem norm_mul_prod_le_of_hasHalvingDecay {φ : G → ℂ} {ι : Type*} (z : ι → G) (N : ι → ℕ)
    (s : Finset ι) (hz : ∀ i ∈ s, HasHalvingDecay φ (z i) (N i)) (a : G) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ e : ι → ℕ, (∀ i ∈ s, e i < N i) → ‖φ (a * ∏ i ∈ s, z i ^ e i)‖ ≤ C)
    (n : ι → ℕ) :
    ‖φ (a * ∏ i ∈ s, z i ^ n i)‖ ≤
      C * (∏ i ∈ s, (2 : ℝ) ^ N i) * (1 / 2) ^ (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty =>
    have := h 0 (by simp)
    simpa using this
  | insert j s hj ih =>
    have hzs : ∀ i ∈ s, HasHalvingDecay φ (z i) (N i) := fun i hi =>
      hz i (Finset.mem_insert_of_mem hi)
    set b : G := a * ∏ i ∈ s, z i ^ n i with hb
    set C' : ℝ := C * (∏ i ∈ s, (2 : ℝ) ^ N i) * (1 / 2) ^ (∑ i ∈ s, n i) with hC'
    have hC'0 : 0 ≤ C' := by positivity
    have hstep : ∀ e < N j, ‖φ (b * z j ^ e)‖ ≤ C' := by
      intro e he
      have hbe : b * z j ^ e = a * z j ^ e * ∏ i ∈ s, z i ^ n i := by
        rw [hb, mul_right_comm]
      rw [hbe]
      refine ih hzs (a * z j ^ e) (fun e' he' => ?_)
      have hupd : ∀ i ∈ insert j s, Function.update e' j e i < N i := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          simpa using he
        · rw [Function.update_of_ne hij]
          exact he' i ((Finset.mem_insert.mp hi).resolve_left hij)
      have hprod : ∏ i ∈ insert j s, z i ^ Function.update e' j e i =
          z j ^ e * ∏ i ∈ s, z i ^ e' i := by
        rw [Finset.prod_insert hj, Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      have := h _ hupd
      rwa [hprod, ← mul_assoc] at this
    have hj' := hz j (Finset.mem_insert_self j s) b C' hC'0 hstep (n j)
    have he : a * ∏ i ∈ insert j s, z i ^ n i = b * z j ^ n j := by
      rw [Finset.prod_insert hj, hb, mul_comm (z j ^ n j), mul_assoc]
    rw [he, Finset.prod_insert hj, Finset.sum_insert hj]
    refine hj'.trans (le_of_eq ?_)
    rw [hC', pow_add]
    ring

end MultiDirection

section Decomposition

/-- **Deep-shell decomposition (real arithmetic).** Let `γ_i ≥ 0` (`i ∈ S`, `S` nonempty, of
cardinality `k`), `Λ > 0`, `η > 0` with `2 k ∑ γ ≤ η Λ`, `M ≥ 0` and `T₀ ∈ ℕ`. Then there is
`R > 0` such that every `v` with `v_i > R` and `v_i > η v_j` (`i, j ∈ S`) can be written
`v_i = (γ_i ∑ n + Λ n_i) + r_i` with `n ∈ ℕ^S`, `∑ n ≥ T₀` and `M ≤ r_i ≤ M + k γ_i + Λ`. -/
theorem exists_shellDecomposition {ι : Type*} (S : Finset ι) (hS : S.Nonempty) {γ : ι → ℝ}
    (hγ : ∀ i ∈ S, 0 ≤ γ i) {Λ η M : ℝ} (hΛ : 0 < Λ) (hη : 0 < η) (hM : 0 ≤ M)
    (hΛη : 2 * S.card * ∑ i ∈ S, γ i ≤ η * Λ) (T₀ : ℕ) :
    ∃ R > 0, ∀ v : ι → ℝ, (∀ i ∈ S, R < v i) → (∀ i ∈ S, ∀ j ∈ S, η * v j < v i) →
      ∃ n : ι → ℕ, T₀ ≤ ∑ i ∈ S, n i ∧ ∀ i ∈ S,
        M ≤ v i - (γ i * ∑ j ∈ S, (n j : ℝ) + Λ * n i) ∧
          v i - (γ i * ∑ j ∈ S, (n j : ℝ) + Λ * n i) ≤ M + S.card * γ i + Λ := by
  set Γ : ℝ := ∑ i ∈ S, γ i with hΓ
  set k : ℝ := (S.card : ℝ) with hk
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg hγ
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast hS.card_pos
  have hΛΓ : 0 < Λ + Γ := by linarith
  have hγΓ : ∀ i ∈ S, γ i ≤ Γ := fun i hi => Finset.single_le_sum hγ hi
  refine ⟨max (2 * M + 1) (M + (T₀ + k) * (Λ + Γ)), by positivity, fun v hR hηv => ?_⟩
  have hv : ∀ i ∈ S, 2 * M + 1 < v i := fun i hi => (le_max_left _ _).trans_lt (hR i hi)
  have hvT : ∀ i ∈ S, M + (T₀ + k) * (Λ + Γ) < v i := fun i hi =>
    (le_max_right _ _).trans_lt (hR i hi)
  set w : ι → ℝ := fun i => v i - M with hw
  set U : ℝ := (∑ i ∈ S, w i) / (Λ + Γ) with hU
  set u : ι → ℝ := fun i => (w i - U * γ i) / Λ with hu
  have hw0 : ∀ i ∈ S, 0 ≤ w i := fun i hi => by simp only [hw]; linarith [hv i hi]
  have hwv : ∀ i ∈ S, w i ≤ v i := fun i hi => by simp only [hw]; linarith
  have hsw0 : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg hw0
  have hU0 : 0 ≤ U := div_nonneg hsw0 hΛΓ.le
  have hUeq : U * (Λ + Γ) = ∑ i ∈ S, w i := div_mul_cancel₀ _ hΛΓ.ne'
  -- `γ_i U ≤ w_i`
  have hγU : ∀ i ∈ S, γ i * U ≤ w i := by
    intro i hi
    have hsumv : η * ∑ j ∈ S, v j ≤ k * v i := by
      rw [Finset.mul_sum, hk, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun j hj => (hηv i hi j hj).le
    have hsumw : ∑ j ∈ S, w j ≤ ∑ j ∈ S, v j := Finset.sum_le_sum hwv
    have hΓU : 0 ≤ Γ * U := mul_nonneg hΓ0 hU0
    have h1 : Λ * (Γ * U) ≤ Γ * ∑ j ∈ S, v j := by
      calc Λ * (Γ * U) ≤ (Λ + Γ) * (Γ * U) := by nlinarith
        _ = Γ * ∑ j ∈ S, w j := by rw [← hUeq]; ring
        _ ≤ Γ * ∑ j ∈ S, v j := mul_le_mul_of_nonneg_left hsumw hΓ0
    have h2 : 2 * k * Γ * (Γ * U) ≤ Γ * (k * v i) := by
      calc 2 * k * Γ * (Γ * U) ≤ η * Λ * (Γ * U) := mul_le_mul_of_nonneg_right hΛη hΓU
        _ = η * (Λ * (Γ * U)) := by ring
        _ ≤ η * (Γ * ∑ j ∈ S, v j) := mul_le_mul_of_nonneg_left h1 hη.le
        _ = Γ * (η * ∑ j ∈ S, v j) := by ring
        _ ≤ Γ * (k * v i) := mul_le_mul_of_nonneg_left hsumv hΓ0
    have h3 : 2 * (Γ * U) ≤ v i := by
      rcases hΓ0.eq_or_lt with hΓz | hΓp
      · rw [← hΓz, zero_mul, mul_zero]
        linarith [hv i hi]
      · have h2' : (k * Γ) * (2 * (Γ * U)) ≤ (k * Γ) * v i := by nlinarith
        exact le_of_mul_le_mul_left h2' (mul_pos hk0 hΓp)
    have h4 : γ i * U ≤ Γ * U := mul_le_mul_of_nonneg_right (hγΓ i hi) hU0
    simp only [hw]
    linarith [hv i hi]
  have hu0 : ∀ i ∈ S, 0 ≤ u i := fun i hi => div_nonneg (by linarith [hγU i hi]) hΛ.le
  have hΛu : ∀ i, Λ * u i = w i - U * γ i := fun i => mul_div_cancel₀ _ hΛ.ne'
  have hsu : ∑ i ∈ S, u i = U := by
    have : Λ * ∑ i ∈ S, u i = Λ * U := by
      rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ => hΛu i, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← hUeq]
      ring
    exact mul_left_cancel₀ hΛ.ne' this
  set n : ι → ℕ := fun i => ⌊u i⌋₊ with hn
  have hnle : ∀ i ∈ S, (n i : ℝ) ≤ u i := fun i hi => Nat.floor_le (hu0 i hi)
  have hnlt : ∀ i, u i < n i + 1 := fun i => Nat.lt_floor_add_one (u i)
  have hsnle : ∑ j ∈ S, (n j : ℝ) ≤ U := hsu ▸ Finset.sum_le_sum hnle
  have hsnlt : U < ∑ j ∈ S, (n j : ℝ) + k := by
    have : ∑ j ∈ S, u j < ∑ j ∈ S, ((n j : ℝ) + 1) :=
      Finset.sum_lt_sum_of_nonempty hS fun j _ => hnlt j
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    rw [← hsu]
    exact this
  refine ⟨n, ?_, fun i hi => ⟨?_, ?_⟩⟩
  · -- the number of steps
    obtain ⟨i₀, hi₀⟩ := hS
    have hUbig : (T₀ + k) < U := by
      have hwi₀ : w i₀ ≤ ∑ j ∈ S, w j := Finset.single_le_sum hw0 hi₀
      have : (T₀ + k) * (Λ + Γ) < U * (Λ + Γ) := by
        rw [hUeq]
        simp only [hw] at hwi₀ ⊢
        linarith [hvT i₀ hi₀]
      exact lt_of_mul_lt_mul_right this hΛΓ.le
    have : (T₀ : ℝ) < ∑ j ∈ S, (n j : ℝ) := by linarith
    have : (T₀ : ℝ) < ((∑ j ∈ S, n j : ℕ) : ℝ) := by rw [Nat.cast_sum]; exact this
    exact_mod_cast this.le
  · -- lower bound
    have h1 : γ i * ∑ j ∈ S, (n j : ℝ) ≤ γ i * U := mul_le_mul_of_nonneg_left hsnle (hγ i hi)
    have h2 : Λ * n i ≤ Λ * u i := mul_le_mul_of_nonneg_left (hnle i hi) hΛ.le
    rw [hΛu i] at h2
    simp only [hw] at h2 ⊢
    linarith
  · -- upper bound
    have h1 : γ i * (U - k) ≤ γ i * ∑ j ∈ S, (n j : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (hγ i hi)
    have h2 : Λ * (u i - 1) ≤ Λ * n i := mul_le_mul_of_nonneg_left (by linarith [hnlt i]) hΛ.le
    rw [mul_sub, hΛu i] at h2
    simp only [hw] at h2 ⊢
    nlinarith

end Decomposition


section Transport

/-- **Precomposition intertwines right translations.** If `f (y x) = f(y) j(x)`, then
`P(ρ(x)) (p ∘ f) = (P(ρ(j x)) p) ∘ f`, `ρ` the right translation. -/
theorem aeval_rightFunctions_comp {A M : Type*} [Group A] [Group M] (f : A → M) (j : A →* M)
    (hf : ∀ y x, f (y * x) = f y * j x) (x : A) (P : ℂ[X]) (p : M → ℂ) :
    aeval (GroupAction.rightFunctions x) P (p ∘ f) =
      (aeval (GroupAction.rightFunctions (j x)) P p) ∘ f := by
  have hpowA : ∀ (k : ℕ) (F : A → ℂ) (y : A),
      ((GroupAction.rightFunctions x) ^ k) F y = F (y * x ^ k) := by
    intro k F y
    rw [← map_pow, GroupAction.rightFunctions_apply]
  have hpowM : ∀ (k : ℕ) (F : M → ℂ) (y : M),
      ((GroupAction.rightFunctions (j x)) ^ k) F y = F (y * j x ^ k) := by
    intro k F y
    rw [← map_pow, GroupAction.rightFunctions_apply]
  have hfpow : ∀ (y : A) (k : ℕ), f (y * x ^ k) = f y * j x ^ k := by
    intro y k
    rw [hf, map_pow]
  funext y
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Function.comp_apply, LinearMap.sum_apply,
    LinearMap.sum_apply, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.smul_apply, Pi.smul_apply, hpowA, hpowM, Function.comp_apply, hfpow]

/-- A monic annihilator of `p` under `ρ(j x)` annihilates `p ∘ f` under `ρ(x)`. -/
theorem aeval_rightFunctions_comp_eq_zero {A M : Type*} [Group A] [Group M] (f : A → M)
    (j : A →* M) (hf : ∀ y x, f (y * x) = f y * j x) {x : A} {P : ℂ[X]} {p : M → ℂ}
    (h : aeval (GroupAction.rightFunctions (j x)) P p = 0) :
    aeval (GroupAction.rightFunctions x) P (p ∘ f) = 0 := by
  rw [aeval_rightFunctions_comp f j hf, h]
  rfl

end Transport

section ShellBound

/-- A function invariant under right translation by an open neighbourhood of `1` closed under
the relevant products is continuous (it is locally constant). -/
theorem continuous_of_mul_right_invariant {M β : Type*} [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] [TopologicalSpace β] {f : M → β} {H : Set M} (hH : IsOpen H)
    (h1 : (1 : M) ∈ H) (hf : ∀ m, ∀ h ∈ H, f (m * h) = f m) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun m => ?_
  have hU : {y : M | m⁻¹ * y ∈ H} ∈ 𝓝 m := by
    refine (hH.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
    simpa using h1
  refine (continuousAt_const (y := f m)).congr ?_
  filter_upwards [hU] with y hy
  have := hf m _ hy
  rw [mul_inv_cancel_left] at this
  exact this.symm

/-- **Bounds on shells via a lattice section.** Let `sec : L → A` be a lattice section with
compact "remainder" set `N` (every `x` is `n · sec c` with `n ∈ N`), let the coordinates
`coord α` (`α ∈ S`) of `x = n · sec c` be the integers `pair α c`, and let `Φ` be continuous and
invariant under the section of the common kernel of the `pair α`. Then `Φ` is bounded above on
every shell `{R₀ < coord α ≤ B, α ∈ S}`. -/
theorem exists_bound_of_latticeSection {A L : Type*} [CommGroup A] [TopologicalSpace A]
    [ContinuousMul A] [AddCommGroup L] (sec : Multiplicative L →* A) {N : Set A}
    (hN : IsCompact N) (hdec : ∀ x : A, ∃ c : L, x * (sec (Multiplicative.ofAdd c))⁻¹ ∈ N)
    {ι : Type*} (S : Finset ι) (coord : ι → A → ℝ) (pair : ι → L →+ ℤ)
    (hcoord : ∀ α ∈ S, ∀ (x : A) (c : L), x * (sec (Multiplicative.ofAdd c))⁻¹ ∈ N →
      coord α x = pair α c)
    {Φ : A → ℝ} (hΦ : Continuous Φ)
    (hΦinv : ∀ (x : A) (c : L), (∀ α ∈ S, pair α c = 0) →
      Φ (x * sec (Multiplicative.ofAdd c)) = Φ x)
    (R₀ B : ℝ) : ∃ C : ℝ, ∀ x : A, (∀ α ∈ S, R₀ < coord α x ∧ coord α x ≤ B) → Φ x ≤ C := by
  classical
  set box : Set (S → ℤ) := Set.pi Set.univ (fun _ => Set.Icc ⌈R₀⌉ ⌊B⌋) with hboxdef
  have hbox : box.Finite := Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  set P : L → (S → ℤ) := fun c α => pair α c with hP
  set rep : (S → ℤ) → L := fun v => if h : ∃ c, P c = v then h.choose else 0 with hrepdef
  set Y : Set A := ⋃ v ∈ box, (fun n => sec (Multiplicative.ofAdd (rep v)) * n) '' N with hY
  have hYc : IsCompact Y :=
    hbox.isCompact_biUnion fun v _ => hN.image (continuous_const.mul continuous_id)
  obtain ⟨C, hC⟩ := hYc.bddAbove_image hΦ.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hdec x
  have hv : P c ∈ box := by
    intro α _
    have h := hx α.1 α.2
    rw [hcoord α.1 α.2 x c hc] at h
    exact ⟨Int.ceil_le.mpr h.1.le, Int.le_floor.mpr h.2⟩
  have hex : ∃ c', P c' = P c := ⟨c, rfl⟩
  have hrep : P (rep (P c)) = P c := by
    simp only [hrepdef, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hκ : ∀ α ∈ S, pair α (c - rep (P c)) = 0 := fun α hα => by
    have := congrFun hrep ⟨α, hα⟩
    simp only [hP] at this
    rw [map_sub, this, sub_self]
  have hx' : x = x * (sec (Multiplicative.ofAdd c))⁻¹ * sec (Multiplicative.ofAdd (rep (P c))) *
      sec (Multiplicative.ofAdd (c - rep (P c))) := by
    rw [mul_assoc _ (sec _), ← map_mul, ← ofAdd_add, add_sub_cancel, inv_mul_cancel_right]
  rw [hx', hΦinv _ _ hκ]
  refine hC ⟨_, ?_, rfl⟩
  refine Set.mem_biUnion hv ⟨x * (sec (Multiplicative.ofAdd c))⁻¹, hc, ?_⟩
  exact mul_comm _ _

end ShellBound

section ParabolicLimit

variable {A E : Type*} [CommGroup A] [AddCommGroup E] [Module ℝ E]

/-- **Abstract parabolic limit from annihilators at strict points.** Let `HM : A → E` be
additive, `S` a finite set of linear forms on `E` and `T` a subgroup of `A`. Assume:
* every `y ∈ T` with `α(HM y) > 0` for all `α ∈ S` admits a monic `P` with roots of modulus at
  most some `θ < 1` and `P(ρ(y)) φ = 0` (`ρ` the right translation);
* there is `g₀ ∈ T` with `α(HM g₀) > 0` for all `α ∈ S`;
* for each `β ∈ S` there is `h β ∈ T` with `β(HM(h β)) = d > 0` and `α(HM(h β)) = 0` for the
  other `α ∈ S`;
* `φ` is bounded on every deep shell `{R₀ < α(HM a) ≤ B, α ∈ S}` (for one fixed `R₀`).
Then `lim_{a →_P ∞} φ(a) = 0`. -/
theorem tendstoZeroAlongParabolic_of_strictAnnihilators {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) {S : Finset (Module.Dual ℝ E)} {φ : A → ℂ}
    (T : Subgroup A)
    (hann : ∀ y ∈ T, (∀ α ∈ S, 0 < α (HM y)) → ∃ P : ℂ[X], P.Monic ∧ ∃ θ < 1,
      (∀ z ∈ P.roots, ‖z‖ ≤ θ) ∧ aeval (GroupAction.rightFunctions y) P φ = 0)
    {g₀ : A} (hg₀T : g₀ ∈ T) (hg₀ : ∀ α ∈ S, 0 < α (HM g₀))
    {d : ℝ} (hd : 0 < d) (h : Module.Dual ℝ E → A) (hhT : ∀ β ∈ S, h β ∈ T)
    (hhβ : ∀ β ∈ S, β (HM (h β)) = d) (hhα : ∀ β ∈ S, ∀ α ∈ S, α ≠ β → α (HM (h β)) = 0)
    (hbdd : ∃ R₀ : ℝ, ∀ B : ℝ, ∃ C : ℝ, ∀ a : A,
      (∀ α ∈ S, R₀ < α (HM a) ∧ α (HM a) ≤ B) → ‖φ a‖ ≤ C) :
    TendstoZeroAlongParabolic HM S φ := by
  classical
  -- additivity of `HM`
  have hHM1 : HM 1 = 0 := by
    have := hHM 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hHMpow : ∀ (x : A) (n : ℕ), HM (x ^ n) = (n : ℝ) • HM x := fun x n => by
    simpa [hHM1] using apply_mul_pow_of_map_mul hHM 1 x n
  have hHMprod : ∀ (s : Finset (Module.Dual ℝ E)) (f : Module.Dual ℝ E → A),
      HM (∏ i ∈ s, f i) = ∑ i ∈ s, HM (f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hHM1]
    | insert j s hj ih => rw [Finset.prod_insert hj, hHM, ih, Finset.sum_insert hj]
  have hHMdiv : ∀ x y : A, HM (x / y) = HM x - HM y := fun x y => by
    have := hHM (x / y) y
    rw [div_mul_cancel] at this
    rw [this, add_sub_cancel_right]
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- no forms: `φ` is bounded, hence `0` by halving along a power of `g₀`
    subst hS
    obtain ⟨R₀, hR₀⟩ := hbdd
    obtain ⟨C, hC⟩ := hR₀ 0
    have hCb : ∀ a, ‖φ a‖ ≤ C := fun a => hC a (by simp)
    obtain ⟨P, hP, θ, hθ, hroots, hP0⟩ := hann g₀ hg₀T (by simp)
    obtain ⟨q₀, hq₀⟩ := exists_hasHalvingDecay_pow hP hθ hroots hP0
    have hzero : ∀ a, φ a = 0 := by
      intro a
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCb a)
      have hb : ∀ n : ℕ, ‖φ a‖ ≤ C * 2 ^ P.natDegree * (1 / 2) ^ n := by
        intro n
        have := hq₀ q₀ le_rfl (a / (g₀ ^ q₀) ^ n) C hC0 (fun e _ => hCb _) n
        rwa [div_mul_cancel] at this
      have ht : Tendsto (fun n : ℕ => C * 2 ^ P.natDegree * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul (C * 2 ^ P.natDegree)
      exact norm_le_zero_iff.mp (ge_of_tendsto' ht hb)
    intro ε hε η _
    exact ⟨1, one_pos, fun a _ _ => by rw [hzero a, norm_zero]; exact hε⟩
  intro ε hε η hη
  set k : ℕ := S.card with hk
  set csum : ℝ := ∑ α ∈ S, α (HM g₀) with hcsum
  have hcsum0 : 0 ≤ csum := Finset.sum_nonneg fun α hα => (hg₀ α hα).le
  -- the length `L = (m + 1) d` of the extra step in the direction `β`
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * k * csum / (η * d))
  set L : ℝ := ((m + 1 : ℕ) : ℝ) * d with hL
  have hL0 : 0 < L := by positivity
  have hLη : 2 * k * csum ≤ η * L := by
    have h1 := (div_le_iff₀ (mul_pos hη hd)).mp hm
    have h2 : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    calc 2 * k * csum ≤ m * (η * d) := h1
      _ ≤ ((m + 1 : ℕ) : ℝ) * (η * d) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = η * L := by rw [hL]; ring
  -- the strict directions `y β = g₀ (h β)^{m+1}`
  set y : Module.Dual ℝ E → A := fun β => g₀ * h β ^ (m + 1) with hy
  have hyT : ∀ β ∈ S, y β ∈ T := fun β hβ => T.mul_mem hg₀T (T.pow_mem (hhT β hβ) _)
  have hycoord : ∀ β ∈ S, ∀ α ∈ S, α (HM (y β)) = α (HM g₀) + if α = β then L else 0 := by
    intro β hβ α hα
    simp only [hy, hHM, hHMpow, map_add, map_smul, smul_eq_mul]
    split_ifs with hαβ
    · subst hαβ
      rw [hhβ α hα, hL]
    · rw [hhα β hβ α hα hαβ, mul_zero]
  have hypos : ∀ β ∈ S, ∀ α ∈ S, 0 < α (HM (y β)) := by
    intro β hβ α hα
    rw [hycoord β hβ α hα]
    have := hg₀ α hα
    split_ifs <;> linarith
  have hhalf : ∀ β ∈ S, ∃ N : ℕ, ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → HasHalvingDecay φ (y β ^ q) N := by
    intro β hβ
    obtain ⟨P, hP, θ, hθ, hroots, hP0⟩ := hann (y β) (hyT β hβ) (hypos β hβ)
    exact ⟨P.natDegree, exists_hasHalvingDecay_pow hP hθ hroots hP0⟩
  choose! N q₀ hN using hhalf
  set q : ℕ := S.sup q₀ + 1 with hq
  have hzhalf : ∀ β ∈ S, HasHalvingDecay φ (y β ^ q) (N β) := fun β hβ =>
    hN β hβ q ((Finset.le_sup hβ).trans (Nat.le_succ _))
  set z : Module.Dual ℝ E → A := fun β => y β ^ q with hz
  set Λ : ℝ := q * L with hΛ
  set γ : Module.Dual ℝ E → ℝ := fun α => q * α (HM g₀) with hγ
  have hq0 : (0 : ℝ) < q := by rw [hq]; positivity
  have hΛ0 : 0 < Λ := mul_pos hq0 hL0
  have hγ0 : ∀ α ∈ S, 0 ≤ γ α := fun α hα => mul_nonneg hq0.le (hg₀ α hα).le
  have hΓ : ∑ α ∈ S, γ α = q * csum := by rw [hcsum, Finset.mul_sum]
  have hΛη : 2 * S.card * ∑ α ∈ S, γ α ≤ η * Λ := by
    rw [hΓ, hΛ]
    have := mul_le_mul_of_nonneg_left hLη hq0.le
    calc 2 * (S.card : ℝ) * (q * csum) = q * (2 * k * csum) := by rw [hk]; ring
      _ ≤ q * (η * L) := this
      _ = η * (q * L) := by ring
  -- coordinates of products of the directions
  have hprod : ∀ e : Module.Dual ℝ E → ℕ, ∀ α ∈ S,
      α (HM (∏ β ∈ S, z β ^ e β)) = γ α * ∑ β ∈ S, (e β : ℝ) + Λ * e α := by
    intro e α hα
    rw [hHMprod, map_sum]
    have hterm : ∀ β ∈ S, α (HM (z β ^ e β)) =
        γ α * e β + if α = β then Λ * e α else 0 := by
      intro β hβ
      simp only [hz]
      rw [← pow_mul, hHMpow, map_smul, smul_eq_mul, hycoord β hβ α hα]
      split_ifs with hαβ
      · subst hαβ
        simp only [hγ, hΛ]
        push_cast
        ring
      · simp only [hγ]
        push_cast
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq]
    simp only [hα, ↓reduceIte]
  -- the deep shell and its bound
  obtain ⟨R₀, hR₀⟩ := hbdd
  set M : ℝ := max R₀ 0 + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  have hMR₀ : R₀ < M := by rw [hM]; linarith [le_max_left R₀ 0]
  set Γ : ℝ := ∑ α ∈ S, γ α with hΓdef
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg hγ0
  set NS : ℝ := ∑ β ∈ S, (N β : ℝ) with hNS
  set B : ℝ := M + k * Γ + Λ + NS * (Γ + Λ) with hB
  obtain ⟨C, hC⟩ := hR₀ B
  set C' : ℝ := max C 0 with hC'
  set K₁ : ℝ := C' * ∏ β ∈ S, (2 : ℝ) ^ N β with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℕ, K₁ * (1 / 2 : ℝ) ^ T₀ < ε := by
    obtain ⟨T₀, hT⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : 0 < K₁ + 1))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨T₀, ?_⟩
    rw [lt_div_iff₀ (by linarith)] at hT
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) T₀]
  obtain ⟨R, hR, hdec⟩ := exists_shellDecomposition S hS hγ0 hΛ0 hη hM0 hΛη T₀
  refine ⟨R, hR, fun a h1 h2 => ?_⟩
  obtain ⟨n, hn, hshell⟩ := hdec (fun α => α (HM a)) h1 h2
  set a' : A := a / ∏ β ∈ S, z β ^ n β with ha'
  have ha : a = a' * ∏ β ∈ S, z β ^ n β := (div_mul_cancel _ _).symm
  have ha'coord : ∀ α ∈ S, α (HM a') = α (HM a) - (γ α * ∑ β ∈ S, (n β : ℝ) + Λ * n α) := by
    intro α hα
    rw [ha', hHMdiv, map_sub, hprod n α hα]
  have hbound := norm_mul_prod_le_of_hasHalvingDecay z N S hzhalf a' (le_max_right C 0)
    (fun e he => ?_) n
  · rw [← ha] at hbound
    calc ‖φ a‖ ≤ C' * (∏ β ∈ S, (2 : ℝ) ^ N β) * (1 / 2) ^ (∑ β ∈ S, n β) := hbound
      _ ≤ K₁ * (1 / 2) ^ T₀ := by
          rw [hK₁]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) (by positivity)
      _ < ε := hT₀
  · -- the points `a' ∏ z^e`, `e < N`, lie in the deep shell
    refine (hC _ fun α hα => ?_).trans (le_max_left C 0)
    rw [hHM, map_add, ha'coord α hα, hprod e α hα]
    obtain ⟨hlo, hhi⟩ := hshell α hα
    have hγα : γ α ≤ Γ := Finset.single_le_sum hγ0 hα
    have he0 : 0 ≤ ∑ β ∈ S, (e β : ℝ) := Finset.sum_nonneg fun β _ => Nat.cast_nonneg _
    have heN : ∑ β ∈ S, (e β : ℝ) ≤ NS :=
      Finset.sum_le_sum fun β hβ => by exact_mod_cast (he β hβ).le
    have heα : (e α : ℝ) ≤ NS := by
      refine le_trans (by exact_mod_cast (he α hα).le) (Finset.single_le_sum
        (f := fun β => (N β : ℝ)) (fun β _ => Nat.cast_nonneg _) hα)
    have hNS0 : 0 ≤ NS := Finset.sum_nonneg fun β _ => Nat.cast_nonneg _
    have hA1 : 0 ≤ γ α * ∑ β ∈ S, (e β : ℝ) + Λ * e α :=
      add_nonneg (mul_nonneg (hγ0 α hα) he0) (mul_nonneg hΛ0.le (Nat.cast_nonneg _))
    have hA2 : γ α * ∑ β ∈ S, (e β : ℝ) + Λ * e α ≤ NS * (Γ + Λ) := by
      have := mul_le_mul hγα heN he0 hΓ0
      have := mul_le_mul_of_nonneg_left heα hΛ0.le
      nlinarith
    have hkγ : (S.card : ℝ) * γ α ≤ k * Γ := by
      rw [hk]; exact mul_le_mul_of_nonneg_left hγα (Nat.cast_nonneg _)
    constructor
    · linarith
    · rw [hB]; linarith

end ParabolicLimit

end Langlands.HarishChandraSchwartz
