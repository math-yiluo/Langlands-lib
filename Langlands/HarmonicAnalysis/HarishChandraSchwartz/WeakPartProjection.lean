import Langlands.HarmonicAnalysis.HarishChandraSchwartz.PositivePartDecay

/-!
# The weak part as a bounded combination of translates

The step "De la majoration déjà démontrée de `(E^G_P sp_χ ψ)_{P'}(m)`, on déduit alors une
majoration analogue pour `(E^G_P sp_χ ψ)^w_{P'}(m')` puis, par différence, la majoration (1)"
in the proof of Waldspurger's Lemma VI.2.3, in an abstract form.

If `F = F^w + F^+` with `p_w(ρ(a)) F^w = 0` and `p_+(ρ(a)) F^+ = 0`, where the roots of `p_w`
have modulus `1` and those of `p_+` modulus at most `θ < 1`, then `F^w = E(ρ(a)) F` for a
polynomial `E` whose degree and coefficients are bounded in terms of the degrees and `θ` only.

* `IsCoeffBounded f d B`: `f` has degree at most `d` and coefficients of norm at most `B`.
* `exists_projection_polynomial`: the uniform polynomial `E` with `p_w ∣ E - 1`, `p_+ ∣ E`.
* `exists_norm_le_sum_translates`: `‖F^w(m)‖ ≤ C Σ_{i ≤ K} ‖F(m aⁱ)‖`.
* `exists_norm_le_exp_of_decomposition`: the abstract Lemma VI.2.3 from a bound on `F`.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial Langlands.HarmonicAnalysis

section Bounds

/-- `f` has degree at most `d` and all its coefficients have norm at most `B`. -/
def IsCoeffBounded (f : ℂ[X]) (d : ℕ) (B : ℝ) : Prop :=
  f.natDegree ≤ d ∧ ∀ k, ‖f.coeff k‖ ≤ B

theorem isCoeffBounded_one : IsCoeffBounded 1 0 1 := by
  refine ⟨by simp, fun k => ?_⟩
  rw [coeff_one]
  split_ifs <;> simp

/-- A partial sum of the norms of the coefficients of `g` is bounded by the sum up to
`natDegree g`. -/
theorem sum_range_norm_coeff_le {g : ℂ[X]} {d : ℕ} (hg : g.natDegree ≤ d) (m : ℕ) :
    ∑ j ∈ Finset.range m, ‖g.coeff j‖ ≤ ∑ j ∈ Finset.range (d + 1), ‖g.coeff j‖ := by
  rcases le_total m (d + 1) with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
      fun _ _ _ => norm_nonneg _
  · refine le_of_eq (Finset.sum_subset (Finset.range_mono h) fun j _ hj' => ?_).symm
    rw [Finset.mem_range, not_lt] at hj'
    rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]

theorem IsCoeffBounded.mul {f g : ℂ[X]} {d₁ d₂ : ℕ} {B₁ B₂ : ℝ}
    (hf : IsCoeffBounded f d₁ B₁) (hg : IsCoeffBounded g d₂ B₂) :
    IsCoeffBounded (f * g) (d₁ + d₂) ((d₂ + 1) * B₁ * B₂) := by
  refine ⟨natDegree_mul_le.trans (add_le_add hf.1 hg.1), fun n => ?_⟩
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hf.2 0)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => f.coeff i * g.coeff j)]
  calc ‖∑ k ∈ Finset.range n.succ, f.coeff k * g.coeff (n - k)‖
      ≤ ∑ k ∈ Finset.range n.succ, ‖f.coeff k‖ * ‖g.coeff (n - k)‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ k ∈ Finset.range n.succ, B₁ * ‖g.coeff (n - k)‖ :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hf.2 k) (norm_nonneg _)
    _ = B₁ * ∑ j ∈ Finset.range n.succ, ‖g.coeff j‖ := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_range_reflect (fun j => ‖g.coeff j‖) n.succ
        simp only [Nat.succ_sub_one] at this
        exact this
    _ ≤ B₁ * ∑ j ∈ Finset.range (d₂ + 1), ‖g.coeff j‖ :=
        mul_le_mul_of_nonneg_left (sum_range_norm_coeff_le hg.1 _) hB₁
    _ ≤ B₁ * ∑ j ∈ Finset.range (d₂ + 1), B₂ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hg.2 j) hB₁
    _ = (d₂ + 1) * B₁ * B₂ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- A product of polynomials bounded by `(d, B)` is bounded by `(card · d, ((d + 1) B)^card)`. -/
theorem isCoeffBounded_multiset_prod {s : Multiset ℂ[X]} {d : ℕ} {B : ℝ}
    (hs : ∀ x ∈ s, IsCoeffBounded x d B) :
    IsCoeffBounded s.prod (Multiset.card s * d) (((d + 1) * B) ^ Multiset.card s) := by
  induction s using Multiset.induction_on with
  | empty => simpa using isCoeffBounded_one
  | cons x t ih =>
    have ht := ih fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have hx := hs x (Multiset.mem_cons_self x t)
    rw [Multiset.prod_cons, mul_comm, Multiset.card_cons]
    have h := ht.mul hx
    refine ⟨h.1.trans (le_of_eq (by ring)), fun k => (h.2 k).trans (le_of_eq ?_)⟩
    rw [pow_succ]
    ring

/-- A monic complex polynomial whose roots have modulus at most `Λ ≥ 1` has coefficients of
norm at most `2^N Λ^N`, `N` its degree. -/
theorem isCoeffBounded_of_roots {p : ℂ[X]} (hp : p.Monic) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ Λ) :
    IsCoeffBounded p p.natDegree (2 ^ p.natDegree * Λ ^ p.natDegree) := by
  refine ⟨le_rfl, fun k => ?_⟩
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  rcases le_or_gt k p.natDegree with hk | hk
  · conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard]
    rw [Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact hk), hcard, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
    have h := norm_esymm_le (s := p.roots) (by linarith) hroots (p.natDegree - k)
    rw [hcard] at h
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΛ (Nat.sub_le _ _))
      (by positivity))
  · rw [coeff_eq_zero_of_natDegree_lt hk, norm_zero]
    have : 0 ≤ Λ := by linarith
    positivity

/-- A product of complex numbers of modulus at least `η ≥ 0` has modulus at least
`η^card`. -/
theorem pow_le_norm_multiset_prod {t : Multiset ℂ} {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ z ∈ t, η ≤ ‖z‖) : η ^ Multiset.card t ≤ ‖t.prod‖ := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons z t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    exact mul_le_mul (hη z (Multiset.mem_cons_self z t))
      (ih fun w hw => hη w (Multiset.mem_cons_of_mem hw)) (pow_nonneg hη0 _)
      (norm_nonneg _)

/-- If the roots of the monic `p` have modulus `1` and `‖w‖ ≤ θ < 1`, then
`‖p(w)‖ ≥ (1 - θ)^N`. -/
theorem pow_le_norm_eval {p : ℂ[X]} (hp : p.Monic) (hroots : ∀ z ∈ p.roots, ‖z‖ = 1)
    {θ : ℝ} (hθ : θ < 1) {w : ℂ} (hw : ‖w‖ ≤ θ) : (1 - θ) ^ p.natDegree ≤ ‖p.eval w‖ := by
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  conv_rhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard]
  rw [eval_multiset_prod, Multiset.map_map]
  have h := pow_le_norm_multiset_prod (t := p.roots.map (eval w ∘ fun a => X - C a))
    (η := 1 - θ) (by linarith) ?_
  · rwa [Multiset.card_map, hcard] at h
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    have h1 := norm_sub_norm_le z w
    rw [hroots z hz, norm_sub_rev] at h1
    linarith

end Bounds

section Projection

/-- `-(p(w))⁻¹ · (p /ₘ (X - w))`: an inverse of `X - w` modulo `p` when `p(w) ≠ 0`. -/
def invXSubCMod (p : ℂ[X]) (w : ℂ) : ℂ[X] :=
  C (-(p.eval w)⁻¹) * (p /ₘ (X - C w))

theorem dvd_X_sub_C_mul_invXSubCMod_sub_one (p : ℂ[X]) {w : ℂ} (hw : p.eval w ≠ 0) :
    p ∣ (X - C w) * invXSubCMod p w - 1 := by
  refine ⟨C (-(p.eval w)⁻¹), ?_⟩
  rw [invXSubCMod, mul_left_comm, X_sub_C_mul_divByMonic_eq_sub_modByMonic,
    modByMonic_X_sub_C_eq_C_eval]
  have h : C (-(p.eval w)⁻¹) * C (p.eval w) = -1 := by
    rw [← C_mul, neg_mul, inv_mul_cancel₀ hw, C_neg, C_1]
  linear_combination -h

/-- Coefficient bound for `invXSubCMod p w`. -/
theorem isCoeffBounded_invXSubCMod {p : ℂ[X]} (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ = 1) {θ : ℝ} (hθ : θ < 1) {w : ℂ}
    (hw : ‖w‖ ≤ θ) :
    IsCoeffBounded (invXSubCMod p w) (p.natDegree - 1)
      (((1 - θ) ^ p.natDegree)⁻¹ * (p.natDegree * 2 ^ p.natDegree)) := by
  have hpb := isCoeffBounded_of_roots hp le_rfl fun z hz => (hroots z hz).le
  simp only [one_pow, mul_one] at hpb
  have hev := pow_le_norm_eval hp hroots hθ hw
  have hpos : 0 < (1 - θ) ^ p.natDegree := pow_pos (by linarith) _
  have hne : p.eval w ≠ 0 := norm_pos_iff.mp (hpos.trans_le hev)
  refine ⟨?_, fun k => ?_⟩
  · refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_divByMonic _ (monic_X_sub_C w), natDegree_X_sub_C]
  · rw [invXSubCMod, coeff_C_mul, norm_mul, norm_neg, norm_inv, coeff_divByMonic_X_sub_C]
    have hw1 : ‖w‖ ≤ 1 := hw.trans hθ.le
    have hsum : ‖∑ i ∈ Finset.Icc (k + 1) p.natDegree, w ^ (i - (k + 1)) * p.coeff i‖ ≤
        p.natDegree * 2 ^ p.natDegree := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i ∈ Finset.Icc (k + 1) p.natDegree, ‖w ^ (i - (k + 1)) * p.coeff i‖
          ≤ ∑ i ∈ Finset.Icc (k + 1) p.natDegree, (2 : ℝ) ^ p.natDegree := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, norm_pow]
            calc ‖w‖ ^ (i - (k + 1)) * ‖p.coeff i‖ ≤ 1 * 2 ^ p.natDegree :=
                  mul_le_mul (pow_le_one₀ (norm_nonneg _) hw1) (hpb.2 i) (norm_nonneg _)
                    zero_le_one
              _ = 2 ^ p.natDegree := one_mul _
        _ = (Finset.Icc (k + 1) p.natDegree).card * 2 ^ p.natDegree := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ p.natDegree * 2 ^ p.natDegree := by
            gcongr
            rw [Nat.card_Icc]
            exact_mod_cast (by omega : p.natDegree + 1 - (k + 1) ≤ p.natDegree)
    calc ‖p.eval w‖⁻¹ * ‖∑ i ∈ Finset.Icc (k + 1) p.natDegree, w ^ (i - (k + 1)) * p.coeff i‖
        ≤ ((1 - θ) ^ p.natDegree)⁻¹ * (p.natDegree * 2 ^ p.natDegree) :=
          mul_le_mul (inv_anti₀ hpos hev) hsum (norm_nonneg _) (inv_nonneg.mpr hpos.le)

/-- A product of polynomials congruent to `1` modulo `p` is congruent to `1` modulo `p`. -/
theorem dvd_multiset_prod_sub_one {p : ℂ[X]} {s : Multiset ℂ[X]}
    (hs : ∀ x ∈ s, p ∣ x - 1) : p ∣ s.prod - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x t ih =>
    have ht := ih fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have hx := hs x (Multiset.mem_cons_self x t)
    rw [Multiset.prod_cons]
    have e : x * t.prod - 1 = x * (t.prod - 1) + (x - 1) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right ht x) hx

/-- **The projection polynomial, uniformly.** For degrees `N_w`, `N_+` and `θ < 1` there is a
constant `C` such that for all monic `p_w`, `p_+` of these degrees, the roots of `p_w` of
modulus `1` and those of `p_+` of modulus at most `θ`, there is `E` of degree at most
`N_+ (N_w - 1) + N_+` with coefficients of norm at most `C`, `p_w ∣ E - 1` and `p_+ ∣ E`. -/
theorem exists_projection_polynomial (Nw Np : ℕ) {θ : ℝ} (hθ : θ < 1) :
    ∃ C : ℝ, ∀ pw pp : ℂ[X], pw.Monic → pp.Monic → pw.natDegree = Nw → pp.natDegree = Np →
      (∀ z ∈ pw.roots, ‖z‖ = 1) → (∀ z ∈ pp.roots, ‖z‖ ≤ θ) →
      ∃ E : ℂ[X], IsCoeffBounded E (Np * (Nw - 1) + Np) C ∧ pw ∣ E - 1 ∧ pp ∣ E := by
  set θ' : ℝ := max θ 0 with hθ'
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθ'1 : θ' < 1 := max_lt hθ (by norm_num)
  set Bq : ℝ := ((1 - θ') ^ Nw)⁻¹ * (Nw * 2 ^ Nw) with hBq
  refine ⟨(Np + 1) * (((Nw - 1 + 1 : ℕ) : ℝ) * Bq) ^ Np * 2 ^ Np,
    fun pw pp hpw hpp hNw hNp hrw hrp => ?_⟩
  have hrp' : ∀ z ∈ pp.roots, ‖z‖ ≤ θ' := fun z hz => (hrp z hz).trans (le_max_left _ _)
  have hcard : Multiset.card pp.roots = Np := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hNp]
  set R : ℂ[X] := (pp.roots.map (invXSubCMod pw)).prod with hR
  refine ⟨R * pp, ?_, ?_, dvd_mul_left pp R⟩
  · -- the bound
    have hRb : IsCoeffBounded R (Np * (Nw - 1)) ((((Nw - 1 + 1 : ℕ) : ℝ) * Bq) ^ Np) := by
      have h := isCoeffBounded_multiset_prod (s := pp.roots.map (invXSubCMod pw))
        (d := Nw - 1) (B := Bq) ?_
      · rw [Multiset.card_map, hcard] at h
        refine ⟨h.1, fun k => (h.2 k).trans (le_of_eq ?_)⟩
        push_cast
        rfl
      · intro x hx
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
        have := isCoeffBounded_invXSubCMod hpw hrw hθ'1 (hrp' w hw)
        rw [hNw] at this
        exact this
    have hpb : IsCoeffBounded pp Np (2 ^ Np) := by
      have h := isCoeffBounded_of_roots hpp le_rfl fun z hz => (hrp' z hz).trans hθ'1.le
      rw [hNp, one_pow, mul_one] at h
      exact h
    have h := hRb.mul hpb
    refine ⟨h.1, fun k => (h.2 k).trans (le_of_eq ?_)⟩
    ring
  · -- `pw ∣ R * pp - 1`
    have hppprod : (pp.roots.map fun a => X - C a).prod = pp :=
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpp IsAlgClosed.card_roots_eq_natDegree
    have e : R * pp = (pp.roots.map fun w => (X - C w) * invXSubCMod pw w).prod := by
      calc R * pp = (pp.roots.map fun a => X - C a).prod * (pp.roots.map (invXSubCMod pw)).prod := by
            rw [hppprod, hR, mul_comm]
        _ = _ := by rw [← Multiset.prod_map_mul]
    rw [e]
    refine dvd_multiset_prod_sub_one fun x hx => ?_
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    have hpos : 0 < (1 - θ') ^ pw.natDegree := pow_pos (by linarith) _
    have hev := pow_le_norm_eval hpw hrw hθ'1 (hrp' w hw)
    exact dvd_X_sub_C_mul_invXSubCMod_sub_one pw (norm_pos_iff.mp (hpos.trans_le hev))

/-- If `x = x_w + x_+` with `p_w(T) x_w = 0` and `p_+(T) x_+ = 0`, and `p_w ∣ E - 1`,
`p_+ ∣ E`, then `E(T) x = x_w`. -/
theorem aeval_apply_eq_of_dvd {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ W)
    {pw pp E : ℂ[X]} (h1 : pw ∣ E - 1) (h2 : pp ∣ E) {x xw xp : W} (hx : x = xw + xp)
    (hw : aeval T pw xw = 0) (hp : aeval T pp xp = 0) : aeval T E x = xw := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨u, hu⟩ := h2
  have hEp : aeval T E xp = 0 := by
    rw [hu, mul_comm, map_mul, Module.End.mul_apply, hp, map_zero]
  have hEw : aeval T E xw = xw := by
    have e : E = 1 + s * pw := by rw [mul_comm, ← hs]; ring
    rw [e, map_add, map_one, map_mul, LinearMap.add_apply, Module.End.mul_apply, hw, map_zero,
      Module.End.one_apply, add_zero]
  rw [hx, map_add, hEw, hEp, add_zero]

variable {G : Type*} [Group G]

/-- **The weak part is bounded by finitely many translates, uniformly.** For degrees `N_w`,
`N_+`, `θ < 1` and `a ∈ G` there is `C` such that, whenever `F = F^w + F^+` with
`p_w(ρ(a)) F^w = 0`, `p_+(ρ(a)) F^+ = 0` (`ρ` the right translation, `p_w`, `p_+` monic of
degrees `N_w`, `N_+`, roots of modulus `1`, resp. at most `θ`),
`‖F^w(m)‖ ≤ C Σ_{i ≤ K} ‖F(m aⁱ)‖` with `K = N_+ (N_w - 1) + N_+`. -/
theorem exists_norm_le_sum_translates (a : G) (Nw Np : ℕ) {θ : ℝ} (hθ : θ < 1) :
    ∃ C : ℝ, ∀ pw pp : ℂ[X], pw.Monic → pp.Monic → pw.natDegree = Nw → pp.natDegree = Np →
      (∀ z ∈ pw.roots, ‖z‖ = 1) → (∀ z ∈ pp.roots, ‖z‖ ≤ θ) →
      ∀ F Fw Fp : G → ℂ, F = Fw + Fp →
        aeval (GroupAction.rightFunctions a) pw Fw = 0 →
        aeval (GroupAction.rightFunctions a) pp Fp = 0 →
        ∀ m, ‖Fw m‖ ≤ C * ∑ i ∈ Finset.range (Np * (Nw - 1) + Np + 1), ‖F (m * a ^ i)‖ := by
  obtain ⟨C, hC⟩ := exists_projection_polynomial Nw Np hθ
  refine ⟨C, fun pw pp hpw hpp hNw hNp hrw hrp F Fw Fp hF hw hp m => ?_⟩
  obtain ⟨E, hEb, hE1, hE2⟩ := hC pw pp hpw hpp hNw hNp hrw hrp
  have hEF := aeval_apply_eq_of_dvd _ hE1 hE2 hF hw hp
  have hpow : ∀ (k : ℕ) (x : G),
      ((GroupAction.rightFunctions a) ^ k) F x = F (x * a ^ k) := by
    intro k x
    rw [← map_pow, GroupAction.rightFunctions_apply]
  have h1 := congrFun hEF m
  rw [aeval_eq_sum_range' (n := Np * (Nw - 1) + Np + 1) (by have := hEb.1; omega),
    LinearMap.sum_apply, Finset.sum_apply] at h1
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hpow] at h1
  rw [← h1]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hEb.2 i) (norm_nonneg _)

end Projection

section Decay

variable {G : Type*} [Group G] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Waldspurger, Lemma VI.2.3, abstract form, from a bound on the constant term.** In the
setting of `exists_norm_le_exp_of_aeval_eq_zero`, let `F i = F^w i + F^+ i` with
`p_w i (ρ(a)) (F^w i) = 0` and `p_+ i (ρ(a)) (F^+ i) = 0`, where the `p_w i` are monic of degree
`N_w` with roots of modulus `1` and the `p_+ i` monic of degree `N_+` with roots of modulus at
most `θ < 1`. If `‖F i g‖ ≤ C₁ B(g) (1 + σ(g))^d` on the shifted chamber and `F^+ i` is bounded
by `C₀ B` on the bounded part of `D(δ)`, then `‖F^+ i g‖ ≤ C B(g) e^{-ε ‖H g‖}` on `D(δ)`. -/
theorem exists_norm_le_exp_of_decomposition {H : G → E}
    (hH : ∀ x y, H (x * y) = H x + H y) {S₀ S : Finset (Module.Dual ℝ E)} {a : G}
    (ha₀ : ∀ β ∈ S₀, β (H a) = 0) (ha : ∀ α ∈ S, 0 < α (H a)) {σ : G → ℝ}
    (hσ0 : ∀ g, 0 ≤ σ g) (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h)
    (hσH : ∃ C : ℝ, ∀ g, 1 + σ g ≤ C * (1 + ‖H g‖)) {B : G → ℝ} (hB0 : ∀ g, 0 ≤ B g)
    (hB : ∀ g, B (g * a) = B g) {ι : Type*} {F Fw Fp : ι → G → ℂ}
    (hF : ∀ i, F i = Fw i + Fp i) {pw pp : ι → ℂ[X]} {Nw Np : ℕ} {θ : ℝ} (hθ : θ < 1)
    (hpw : ∀ i, (pw i).Monic) (hpp : ∀ i, (pp i).Monic) (hNw : ∀ i, (pw i).natDegree = Nw)
    (hNp : ∀ i, (pp i).natDegree = Np) (hrw : ∀ i, ∀ z ∈ (pw i).roots, ‖z‖ = 1)
    (hrp : ∀ i, ∀ z ∈ (pp i).roots, ‖z‖ ≤ θ)
    (hannw : ∀ i, aeval (GroupAction.rightFunctions a) (pw i) (Fw i) = 0)
    (hannp : ∀ i, aeval (GroupAction.rightFunctions a) (pp i) (Fp i) = 0)
    {t : ℝ} (ht : 0 ≤ t) {C₁ : ℝ} {d : ℕ}
    (h1 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, t ≤ α (H g)) →
      ‖F i g‖ ≤ C₁ * B g * (1 + σ g) ^ d)
    {δ : ℝ} (hδ : 0 < δ) {C₀ : ℝ}
    (h0 : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) →
      ‖H g‖ ≤ t / δ → ‖Fp i g‖ ≤ C₀ * B g) :
    ∃ ε > 0, ∃ C : ℝ, ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, δ * ‖H g‖ ≤ α (H g)) →
      ‖Fp i g‖ ≤ C * B g * Real.exp (-(ε * ‖H g‖)) := by
  obtain ⟨Cw, hCw⟩ := exists_norm_le_sum_translates a Nw Np hθ
  set K : ℕ := Np * (Nw - 1) + Np + 1 with hK
  have hHpow : ∀ (g : G) (n : ℕ), H (g ^ n) = (n : ℝ) • H g := map_pow_of_additive hH
  have hBa : ∀ (g : G) (n : ℕ), B (g * a ^ n) = B g := by
    intro g n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, hB, ih]
  set C₁' : ℝ := |C₁| * (1 + σ 1) ^ d + |Cw| * ∑ n ∈ Finset.range K, |C₁| * (1 + σ (a ^ n)) ^ d
    with hC₁'
  -- estimate (1) for the positive part
  have h1p : ∀ i g, (∀ β ∈ S₀, 0 ≤ β (H g)) → (∀ α ∈ S, t ≤ α (H g)) →
      ‖Fp i g‖ ≤ C₁' * B g * (1 + σ g) ^ d := by
    intro i g hg0 hgt
    have hσg : 0 ≤ 1 + σ g := by linarith [hσ0 g]
    have hBd : 0 ≤ B g * (1 + σ g) ^ d := mul_nonneg (hB0 g) (pow_nonneg hσg d)
    have hFn : ∀ n : ℕ, ‖F i (g * a ^ n)‖ ≤ |C₁| * (1 + σ (a ^ n)) ^ d * (B g * (1 + σ g) ^ d) := by
      intro n
      have hgn0 : ∀ β ∈ S₀, 0 ≤ β (H (g * a ^ n)) := by
        intro β hβ
        rw [hH, hHpow, map_add, map_smul, ha₀ β hβ, smul_zero, add_zero]
        exact hg0 β hβ
      have hgnt : ∀ α ∈ S, t ≤ α (H (g * a ^ n)) := by
        intro α hα
        rw [hH, hHpow, map_add, map_smul, smul_eq_mul]
        linarith [hgt α hα, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (ha α hα).le]
      have h := h1 i (g * a ^ n) hgn0 hgnt
      rw [hBa] at h
      have hσmul : 1 + σ (g * a ^ n) ≤ (1 + σ g) * (1 + σ (a ^ n)) := by
        nlinarith [hσ g (a ^ n), hσ0 g, hσ0 (a ^ n), mul_nonneg (hσ0 g) (hσ0 (a ^ n))]
      have hσgn : 0 ≤ 1 + σ (g * a ^ n) := by linarith [hσ0 (g * a ^ n)]
      calc ‖F i (g * a ^ n)‖ ≤ C₁ * B g * (1 + σ (g * a ^ n)) ^ d := h
        _ ≤ |C₁| * B g * ((1 + σ g) * (1 + σ (a ^ n))) ^ d :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C₁) (hB0 g))
              (pow_le_pow_left₀ hσgn hσmul d) (pow_nonneg hσgn d)
              (mul_nonneg (abs_nonneg _) (hB0 g))
        _ = |C₁| * (1 + σ (a ^ n)) ^ d * (B g * (1 + σ g) ^ d) := by rw [mul_pow]; ring
    have hw := hCw (pw i) (pp i) (hpw i) (hpp i) (hNw i) (hNp i) (hrw i) (hrp i) (F i) (Fw i)
      (Fp i) (hF i) (hannw i) (hannp i) g
    have hFp : Fp i g = F i g - Fw i g := by
      rw [hF i, Pi.add_apply]
      ring
    have hF0 := hFn 0
    simp only [pow_zero, mul_one] at hF0
    have hsum : ∑ n ∈ Finset.range K, ‖F i (g * a ^ n)‖ ≤
        (∑ n ∈ Finset.range K, |C₁| * (1 + σ (a ^ n)) ^ d) * (B g * (1 + σ g) ^ d) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun n _ => hFn n
    calc ‖Fp i g‖ = ‖F i g - Fw i g‖ := by rw [hFp]
      _ ≤ ‖F i g‖ + ‖Fw i g‖ := norm_sub_le _ _
      _ ≤ |C₁| * (1 + σ 1) ^ d * (B g * (1 + σ g) ^ d) +
            |Cw| * ((∑ n ∈ Finset.range K, |C₁| * (1 + σ (a ^ n)) ^ d) *
              (B g * (1 + σ g) ^ d)) := by
          refine add_le_add hF0 (hw.trans ?_)
          exact mul_le_mul (le_abs_self Cw) hsum
            (Finset.sum_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _)
      _ = C₁' * B g * (1 + σ g) ^ d := by rw [hC₁']; ring
  exact exists_norm_le_exp_of_aeval_eq_zero hH ha₀ ha hσ0 hσ hσH hB0 hB hθ hpp hNp hrp hannp
    ht h1p hδ h0

end Decay

end Langlands.HarishChandraSchwartz
