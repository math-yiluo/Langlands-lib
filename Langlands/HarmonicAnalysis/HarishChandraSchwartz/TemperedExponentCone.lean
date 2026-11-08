import Langlands.Representation.Jacquet.StablePairingAsymptotics
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedTwistIntegrability
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Exponents of tempered representations lie in the closed positive cone

The implication (i) ⇒ (ii) of Waldspurger's Proposition III.2.2, in an abstract form
with explicit hypotheses: for a smooth representation with tempered coefficients, the
real part of every exponent of a Jacquet module lies in the closed cone `+ā_P^{G*}`
spanned by the simple roots.

* `closedPositiveCone S` is the set of combinations `∑_{α ∈ S} x_α α` with `x_α ≥ 0`.
* `mem_closedPositiveCone_of_norm_le_one`: for a character `χ` of an abstract group `A`
  with `|χ(a)| = q^{-⟨λ, H_M(a)⟩}`, if `|χ(a)| ≤ 1` whenever `⟨α, H_M(a)⟩ > 0` for all
  `α ∈ S`, then `λ ∈ closedPositiveCone S` (`H_M(A)` spans, `S` linearly independent).
* `norm_lt_one_of_norm_le_one`: a character with `|χ| ≤ 1` on the open chamber and
  `|χ(b)| ≠ 1` for some `b` satisfies `|χ(a₀)| < 1` at every point `a₀` of the chamber.
* `norm_le_of_stablePairing_eigenvector`: for supplied `StablePairingData` satisfying
  `Admits`, an eigenvalue `ν` of `g⁻¹` on the opposite quotient satisfies `|ν| ≤ c` as
  soon as the matrix coefficients along `g⁻ʳ` are `O(c^r (1 + r)^k)`.
* `norm_le_one_of_hasTemperedCoefficients`: for tempered coefficients, a generalized eigenvalue
  of the normalized Jacquet action of one element `m` has modulus at most `1`.
* `mem_closedPositiveCone_of_hasTemperedCoefficients`: the combination, from tempered
  coefficients, an upper bound for `Ξ` on the open chamber and pairing data along every
  element of the open chamber.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open scoped NNReal
open Filter Langlands.Jacquet

section Cone

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The closed cone `+ā_P^{G*}` of Waldspurger I.1: the linear forms `∑_{α ∈ S} x_α α`
with all `x_α ≥ 0`. -/
def closedPositiveCone (S : Finset (Module.Dual ℝ E)) : Set (Module.Dual ℝ E) :=
  {lam | ∃ x : Module.Dual ℝ E → ℝ, (∀ α ∈ S, 0 ≤ x α) ∧ lam = ∑ α ∈ S, x α • α}

/-- Replacing the coordinates of `n H` in a basis by their integer parts changes the value
of a linear form `φ` by at most `∑_i |φ(b_i)|`. -/
theorem abs_natCast_mul_sub_le {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (H : E)
    (n : ℕ) (φ : Module.Dual ℝ E) :
    |(n : ℝ) * φ H - φ (∑ i, ⌊(n : ℝ) * b.repr H i⌋ • b i)| ≤ ∑ i, |φ (b i)| := by
  have hH : φ H = ∑ i, b.repr H i * φ (b i) := by
    conv_lhs => rw [← b.sum_repr H]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have hx : φ (∑ i, ⌊(n : ℝ) * b.repr H i⌋ • b i) =
      ∑ i, (⌊(n : ℝ) * b.repr H i⌋ : ℝ) * φ (b i) := by
    simp [map_sum, map_zsmul, zsmul_eq_mul]
  rw [hH, hx, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have e : (n : ℝ) * (b.repr H i * φ (b i)) - (⌊(n : ℝ) * b.repr H i⌋ : ℝ) * φ (b i) =
      Int.fract ((n : ℝ) * b.repr H i) * φ (b i) := by
    rw [Int.fract]
    ring
  rw [e, abs_mul, abs_of_nonneg (Int.fract_nonneg _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (Int.fract_lt_one _).le

/-- **Density step.** If an additive subgroup `Λ` spans `E`, a linear form which is
nonnegative at the points of `Λ` in the open chamber `{α > 0, α ∈ S}` is nonnegative on
the whole open chamber. -/
theorem nonneg_of_forall_mem_openChamber [FiniteDimensional ℝ E] {Λ : AddSubgroup E}
    (hΛ : Submodule.span ℝ (Λ : Set E) = ⊤) {S : Finset (Module.Dual ℝ E)}
    {lam : Module.Dual ℝ E} (h : ∀ x ∈ Λ, (∀ α ∈ S, 0 < α x) → 0 ≤ lam x) {H : E}
    (hH : ∀ α ∈ S, 0 < α H) : 0 ≤ lam H := by
  classical
  obtain ⟨t, htΛ, htspan, hli⟩ := exists_linearIndependent ℝ (Λ : Set E)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ((↑) : t → E)) := by
    rw [Subtype.range_coe, htspan, hΛ]
  let b : Module.Basis t ℝ E := Module.Basis.mk hli hsp
  have : Fintype t := FiniteDimensional.fintypeBasisIndex b
  have hb : ∀ i, b i ∈ Λ := fun i => by
    rw [Module.Basis.mk_apply]
    exact htΛ i.2
  have hxΛ : ∀ n : ℕ, (∑ i, ⌊(n : ℝ) * b.repr H i⌋ • b i) ∈ Λ := fun n =>
    AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hb i) _
  by_contra hneg
  push Not at hneg
  set B : Module.Dual ℝ E → ℝ := fun φ => ∑ i, |φ (b i)| with hBdef
  have hBnn : ∀ φ, 0 ≤ B φ := fun φ => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsum_nn : 0 ≤ ∑ α ∈ S, B α / α H :=
    Finset.sum_nonneg fun β hβ => div_nonneg (hBnn β) (hH β hβ).le
  have hlam_nn : 0 ≤ B lam / (-lam H) := div_nonneg (hBnn lam) (neg_pos.mpr hneg).le
  obtain ⟨n, hn⟩ := exists_nat_gt (∑ α ∈ S, B α / α H + B lam / (-lam H))
  set x : E := ∑ i, ⌊(n : ℝ) * b.repr H i⌋ • b i with hxdef
  have hpos : ∀ α ∈ S, 0 < α x := by
    intro α hα
    have h1 := (abs_le.mp (abs_natCast_mul_sub_le b H n α)).2
    have hterm : B α / α H ≤ ∑ α ∈ S, B α / α H :=
      Finset.single_le_sum (f := fun α => B α / α H)
        (fun β hβ => div_nonneg (hBnn β) (hH β hβ).le) hα
    have h2 : B α / α H < n := by linarith
    have h3 : B α < n * α H := by rwa [div_lt_iff₀ (hH α hα)] at h2
    linarith
  have hlam : lam x < 0 := by
    have h1 := (abs_le.mp (abs_natCast_mul_sub_le b H n lam)).1
    have h2 : B lam / (-lam H) < n := by linarith
    have h3 : B lam < n * (-lam H) := by rwa [div_lt_iff₀ (neg_pos.mpr hneg)] at h2
    linarith
  exact absurd (h x (hxΛ n) hpos) (not_le.mpr hlam)

/-- **Closure step.** If the open chamber `{α > 0, α ∈ S}` is nonempty, a linear form which
is nonnegative on it is nonnegative on the closed chamber `{α ≥ 0, α ∈ S}`. -/
theorem nonneg_of_forall_openChamber {S : Finset (Module.Dual ℝ E)} {lam : Module.Dual ℝ E}
    {H₀ : E} (hH₀ : ∀ α ∈ S, 0 < α H₀) (h : ∀ H, (∀ α ∈ S, 0 < α H) → 0 ≤ lam H) {H : E}
    (hH : ∀ α ∈ S, 0 ≤ α H) : 0 ≤ lam H := by
  by_contra hneg
  push Not at hneg
  set t : ℝ := -lam H / (2 * (|lam H₀| + 1)) with ht
  have hden : 0 < 2 * (|lam H₀| + 1) := by positivity
  have htpos : 0 < t := div_pos (neg_pos.mpr hneg) hden
  have h1 := h (H + t • H₀) fun α hα => by
    rw [map_add, map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (hH α hα) (mul_pos htpos (hH₀ α hα))
  rw [map_add, map_smul, smul_eq_mul] at h1
  have h2 : t * lam H₀ ≤ t * |lam H₀| := mul_le_mul_of_nonneg_left (le_abs_self _) htpos.le
  have h3 : t * (2 * (|lam H₀| + 1)) = -lam H := div_mul_cancel₀ _ hden.ne'
  nlinarith

/-- **Dual cone of a linearly independent family.** If `S` is linearly independent and
`λ` is nonnegative on the closed chamber `{α ≥ 0, α ∈ S}`, then `λ = ∑_{α ∈ S} x_α α`
with all `x_α ≥ 0`. -/
theorem mem_closedPositiveCone_of_nonneg [FiniteDimensional ℝ E]
    {S : Finset (Module.Dual ℝ E)} (hS : LinearIndependent ℝ ((↑) : S → Module.Dual ℝ E))
    {lam : Module.Dual ℝ E} (h : ∀ H, (∀ α ∈ S, 0 ≤ α H) → 0 ≤ lam H) :
    lam ∈ closedPositiveCone S := by
  classical
  let L : E →ₗ[ℝ] (S → ℝ) := LinearMap.pi fun α : S => (α : Module.Dual ℝ E)
  have hLapply : ∀ H (α : S), L H α = (α : Module.Dual ℝ E) H := fun H α => rfl
  have hL : Function.Surjective L := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hc : ∀ α : S, φ (Pi.single α 1) = 0 := by
      have hsum : ∑ α : S, φ (Pi.single α 1) • (α : Module.Dual ℝ E) = 0 := by
        ext H
        have h0 := LinearMap.congr_fun hφ H
        rw [LinearMap.dualMap_apply, LinearMap.zero_apply] at h0
        have e : L H = ∑ α : S, (α : Module.Dual ℝ E) H • Pi.single α (1 : ℝ) := by
          ext β
          simp [hLapply, Finset.sum_apply, Pi.single_apply]
        rw [e, map_sum] at h0
        simp only [map_smul, smul_eq_mul] at h0
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
          LinearMap.zero_apply]
        rw [← h0]
        exact Finset.sum_congr rfl fun α _ => mul_comm _ _
      exact fun α => Fintype.linearIndependent_iff.mp hS _ hsum α
    refine LinearMap.pi_ext fun α c => ?_
    have e : (Pi.single α c : S → ℝ) = c • Pi.single α 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e, map_smul, hc α, smul_zero, LinearMap.zero_apply]
  choose Hb hHb using fun β : S => hL (Pi.single β 1)
  have hHbα : ∀ α β : S, (α : Module.Dual ℝ E) (Hb β) = if α = β then 1 else 0 := by
    intro α β
    rw [← hLapply, hHb β, Pi.single_apply]
  refine ⟨fun α => if hα : α ∈ S then lam (Hb ⟨α, hα⟩) else 0, ?_, ?_⟩
  · intro α hα
    simp only [hα, dite_true]
    refine h _ fun γ hγ => ?_
    have := hHbα ⟨γ, hγ⟩ ⟨α, hα⟩
    simp only at this
    rw [this]
    split_ifs <;> norm_num
  · ext H
    set H' : E := H - ∑ β : S, (β : Module.Dual ℝ E) H • Hb β with hH'
    have hα0 : ∀ α ∈ S, α H' = 0 := by
      intro α hα
      rw [hH', map_sub, map_sum]
      simp only [map_smul, smul_eq_mul]
      have e : ∑ β : S, (β : Module.Dual ℝ E) H * α (Hb β) = α H := by
        have := Finset.sum_ite_eq' (Finset.univ : Finset S) (⟨α, hα⟩ : S)
          (fun β : S => (β : Module.Dual ℝ E) H)
        simp only [Finset.mem_univ, ite_true] at this
        rw [← this]
        refine Finset.sum_congr rfl fun β _ => ?_
        have h1 := hHbα ⟨α, hα⟩ β
        simp only at h1
        rw [h1]
        split_ifs with h2 h3 h3
        · simp
        · exact absurd h2.symm h3
        · exact absurd h3.symm h2
        · simp
      rw [e, sub_self]
    have hlamH' : lam H' = 0 := by
      have h1 := h H' fun α hα => (hα0 α hα).ge
      have h2 := h (-H') fun α hα => by rw [map_neg, hα0 α hα, neg_zero]
      rw [map_neg] at h2
      linarith
    have hlamH : lam H = ∑ β : S, (β : Module.Dual ℝ E) H * lam (Hb β) := by
      have e : H = H' + ∑ β : S, (β : Module.Dual ℝ E) H • Hb β := by
        rw [hH', sub_add_cancel]
      conv_lhs => rw [e]
      rw [map_add, hlamH', zero_add, map_sum]
      simp only [map_smul, smul_eq_mul]
    rw [hlamH, LinearMap.sum_apply, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [β.2, dite_true, LinearMap.smul_apply, smul_eq_mul, Subtype.coe_eta]
    ring

end Cone

section Character

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {A : Type*} [CommGroup A]

/-- **Exponent cone from the bound `|χ| ≤ 1` on the open chamber** (Waldspurger,
Proposition III.2.2, proof of (i) ⇒ (ii), the last step). Let `H_M : A → E` be additive
with `H_M(A)` spanning `E`, `S` a linearly independent finite set of linear forms, `a₀` with
`⟨α, H_M(a₀)⟩ > 0` for all `α ∈ S`, and `χ : A →* ℂˣ` with `|χ(a)| = q^{-⟨λ, H_M(a)⟩}`
for some `q > 1`. If `|χ(a)| ≤ 1` whenever `⟨α, H_M(a)⟩ > 0` for all `α ∈ S`, then
`λ ∈ closedPositiveCone S`. -/
theorem mem_closedPositiveCone_of_norm_le_one [FiniteDimensional ℝ E] {HM : A → E}
    (hHM : ∀ a b, HM (a * b) = HM a + HM b) (hspan : Submodule.span ℝ (Set.range HM) = ⊤)
    {S : Finset (Module.Dual ℝ E)} (hS : LinearIndependent ℝ ((↑) : S → Module.Dual ℝ E))
    {a₀ : A} (ha₀ : ∀ α ∈ S, 0 < α (HM a₀)) {χ : A →* ℂˣ} {q : ℝ} (hq : 1 < q)
    {lam : Module.Dual ℝ E} (hlam : ∀ a, ‖(χ a : ℂ)‖ = q ^ (-lam (HM a)))
    (h1 : ∀ a, (∀ α ∈ S, 0 < α (HM a)) → ‖(χ a : ℂ)‖ ≤ 1) :
    lam ∈ closedPositiveCone S := by
  let f : Additive A →+ E := AddMonoidHom.mk' (fun a => HM a.toMul) fun a b => hHM _ _
  have hrange : ((f.range : AddSubgroup E) : Set E) = Set.range HM := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.toMul, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Additive.ofMul a, rfl⟩
  have hΛ : ∀ x ∈ f.range, (∀ α ∈ S, 0 < α x) → 0 ≤ lam x := by
    rintro x ⟨a, rfl⟩ hx
    have ha := h1 a.toMul hx
    rw [hlam, ← Real.rpow_zero q] at ha
    have := (Real.rpow_le_rpow_left_iff hq).mp ha
    change 0 ≤ lam (HM a.toMul)
    linarith
  refine mem_closedPositiveCone_of_nonneg hS fun H hH => ?_
  refine nonneg_of_forall_openChamber ha₀ (fun H' hH' => ?_) hH
  exact nonneg_of_forall_mem_openChamber (by rw [hrange, hspan]) hΛ hH'

/-- **A non-unitary character is strictly contracting inside the chamber.** Let `H_M : A → E`
be additive and `a₀` with `⟨α, H_M(a₀)⟩ > 0` for all `α ∈ S`. If `|χ(a)| ≤ 1` whenever
`⟨α, H_M(a)⟩ > 0` for all `α ∈ S`, and `|χ(b)| ≠ 1` for some `b`, then `|χ(a₀)| < 1`. -/
theorem norm_lt_one_of_norm_le_one {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b)
    {S : Finset (Module.Dual ℝ E)} {a₀ : A} (ha₀ : ∀ α ∈ S, 0 < α (HM a₀)) {χ : A →* ℂˣ}
    (h1 : ∀ a, (∀ α ∈ S, 0 < α (HM a)) → ‖(χ a : ℂ)‖ ≤ 1) (hne : ∃ b, ‖(χ b : ℂ)‖ ≠ 1) :
    ‖(χ a₀ : ℂ)‖ < 1 := by
  have hH1 : HM 1 = 0 := by simpa using hHM 1 1
  have hpow : ∀ n : ℕ, HM (a₀ ^ n) = (n : ℝ) • HM a₀ := by
    intro n
    induction n with
    | zero => rw [pow_zero, hH1, Nat.cast_zero, zero_smul]
    | succ n ih => rw [pow_succ, hHM, ih, Nat.cast_succ, add_smul, one_smul]
  have hev : ∀ c : A, ∀ᶠ n : ℕ in atTop, ∀ α ∈ S, 0 < α (HM (a₀ ^ n * c)) := by
    intro c
    rw [Filter.eventually_all_finset]
    intro α hα
    have ht : Tendsto (fun n : ℕ => (n : ℝ) * α (HM a₀) + α (HM c)) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.atTop_mul_const (ha₀ α hα))
    filter_upwards [ht.eventually_gt_atTop 0] with n hn
    rw [hHM, map_add, hpow, map_smul, smul_eq_mul]
    exact hn
  have hle : ‖(χ a₀ : ℂ)‖ ≤ 1 := h1 a₀ ha₀
  refine lt_of_le_of_ne hle fun heq => ?_
  have hnorm : ∀ (n : ℕ) (c : A), ‖(χ (a₀ ^ n * c) : ℂ)‖ = ‖(χ c : ℂ)‖ := by
    intro n c
    rw [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, heq,
      one_pow, one_mul]
  obtain ⟨b, hb⟩ := hne
  obtain ⟨n₁, hn₁⟩ := (hev b).exists
  obtain ⟨n₂, hn₂⟩ := (hev b⁻¹).exists
  have hb1 : ‖(χ b : ℂ)‖ ≤ 1 := by rw [← hnorm n₁ b]; exact h1 _ hn₁
  have hb2 : ‖(χ b⁻¹ : ℂ)‖ ≤ 1 := by rw [← hnorm n₂ b⁻¹]; exact h1 _ hn₂
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at hb2
  have hpos : 0 < ‖(χ b : ℂ)‖ := norm_pos_iff.mpr (χ b).ne_zero
  exact hb (le_antisymm hb1 ((inv_le_one₀ hpos).mp hb2))

end Character

section Growth

/-- A real `x` with `x^r K ≤ C c^r (1 + r)^k` for all large `r`, where `K, c > 0`,
satisfies `x ≤ c`. -/
theorem le_of_eventually_pow_mul_le {x c K C : ℝ} {k : ℕ} (hc : 0 < c)
    (hK : 0 < K) (h : ∀ᶠ r : ℕ in atTop, x ^ r * K ≤ C * c ^ r * (1 + r) ^ k) : x ≤ c := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  set y := x / c with hydef
  have hxy : x = y * c := by rw [hydef, div_mul_cancel₀ _ hc.ne']
  suffices hy : y ≤ 1 by
    rw [hxy]
    nlinarith
  by_contra hy1
  push Not at hy1
  have hy0 : 0 < y := by linarith
  have hyN : 0 < y ^ N := pow_pos hy0 N
  refine absurd (le_one_of_pow_le k (D := |C| / K * (1 + N) ^ k / y ^ N) fun n => ?_)
    (not_le.mpr hy1)
  have h1 := hN (N + n) le_self_add
  rw [hxy, mul_pow] at h1
  have hcpow : 0 < c ^ (N + n) := pow_pos hc _
  have h2 : y ^ (N + n) * K ≤ C * (1 + ((N + n : ℕ) : ℝ)) ^ k := by
    have h' : c ^ (N + n) * (y ^ (N + n) * K) ≤
        c ^ (N + n) * (C * (1 + ((N + n : ℕ) : ℝ)) ^ k) := by
      calc c ^ (N + n) * (y ^ (N + n) * K) = y ^ (N + n) * c ^ (N + n) * K := by ring
        _ ≤ C * c ^ (N + n) * (1 + ((N + n : ℕ) : ℝ)) ^ k := h1
        _ = c ^ (N + n) * (C * (1 + ((N + n : ℕ) : ℝ)) ^ k) := by ring
    exact le_of_mul_le_mul_left h' hcpow
  have h3 : (1 + ((N + n : ℕ) : ℝ)) ^ k ≤ ((1 + N) * (1 + n)) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N), (n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h4 : C * (1 + ((N + n : ℕ) : ℝ)) ^ k ≤ |C| * ((1 + N) ^ k * (1 + n) ^ k) := by
    rw [← mul_pow]
    calc C * (1 + ((N + n : ℕ) : ℝ)) ^ k ≤ |C| * (1 + ((N + n : ℕ) : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + N) * (1 + n)) ^ k := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
  rw [pow_add] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hyN, div_mul_eq_mul_div, div_mul_eq_mul_div,
    le_div_iff₀ hK]
  calc y ^ n * y ^ N * K = y ^ N * y ^ n * K := by ring
    _ ≤ |C| * ((1 + N) ^ k * (1 + n) ^ k) := h2.trans h4
    _ = |C| * (1 + N) ^ k * (1 + n) ^ k := by ring

variable {G : Type*} [Group G]

/-- For a nonnegative subadditive `σ` and a real exponent `s`, the powers of `g` satisfy
`(1 + σ(gⁿ))^s ≤ (1 + σ(1) + σ(g))^{|s|} (1 + n)^{⌈|s|⌉}`. -/
theorem one_add_rpow_le_of_subadditive {σ : G → ℝ} (hσ0 : ∀ g, 0 ≤ σ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) (g : G) (s : ℝ) (n : ℕ) :
    (1 + σ (g ^ n)) ^ s ≤ (1 + σ 1 + σ g) ^ |s| * (1 + n) ^ ⌈|s|⌉₊ := by
  set B : ℝ := 1 + σ 1 + σ g with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith [hσ0 1, hσ0 g]
  have hσn : 1 + σ (g ^ n) ≤ B * (1 + n) := by
    have h1 := le_add_nsmul_of_subadditive hσ g n
    have h2 := hσ0 g
    have h3 := hσ0 1
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith
  have hy1 : 1 ≤ 1 + σ (g ^ n) := by linarith [hσ0 (g ^ n)]
  have hn1 : (1 : ℝ) ≤ 1 + n := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hk : |s| ≤ (⌈|s|⌉₊ : ℝ) := Nat.le_ceil _
  calc (1 + σ (g ^ n)) ^ s ≤ (1 + σ (g ^ n)) ^ |s| :=
        Real.rpow_le_rpow_of_exponent_le hy1 (le_abs_self s)
    _ ≤ (B * (1 + n)) ^ |s| := Real.rpow_le_rpow (by linarith) hσn (abs_nonneg s)
    _ = B ^ |s| * (1 + n) ^ |s| := Real.mul_rpow (by linarith) (by linarith)
    _ ≤ B ^ |s| * (1 + n) ^ (⌈|s|⌉₊ : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hk)
          (Real.rpow_nonneg (by linarith) _)
    _ = B ^ |s| * (1 + n) ^ ⌈|s|⌉₊ := by rw [Real.rpow_natCast]

/-- A generalized eigenvector gives an eigenvector for the same eigenvalue. -/
theorem exists_apply_eq_smul_of_pow_apply_eq_zero {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : Module.End ℂ W) (μ : ℂ) {y : W} (hy : y ≠ 0) {k : ℕ}
    (hk : ((T - μ • (1 : Module.End ℂ W)) ^ k) y = 0) : ∃ w, w ≠ 0 ∧ T w = μ • w := by
  classical
  have hex : ∃ n, ((T - μ • (1 : Module.End ℂ W)) ^ n) y = 0 := ⟨k, hk⟩
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, Module.End.one_apply] at this
    exact hy this
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hn0
  refine ⟨((T - μ • (1 : Module.End ℂ W)) ^ m) y, Nat.find_min hex (by omega), ?_⟩
  have h : (T - μ • (1 : Module.End ℂ W)) (((T - μ • (1 : Module.End ℂ W)) ^ m) y) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', ← hm]
    exact Nat.find_spec hex
  rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at h
  exact h

end Growth

section StablePairing

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}

/-- **Eigenvalues on the opposite quotient are bounded by the growth of coefficients.**
For `StablePairingData` `D` satisfying `Admits` and a vector `v` whose class in the
opposite quotient is nonzero with `[ρ(g⁻ʳ) v] = νʳ [v]` for all `r`, if every matrix
coefficient `ℓ(ρ(g⁻ʳ) v)` is eventually at most `C c^r (1 + r)^k` with `c > 0`, then
`|ν| ≤ c`. -/
theorem norm_le_of_stablePairing_eigenvector (D : StablePairingData G) (hA : D.Admits ρ hρ)
    {v : V} (hv : Jacquet.mk ρ D.Nbar v ≠ 0) {ν : ℂ}
    (hν : ∀ r : ℕ, Jacquet.mk ρ D.Nbar (ρ (D.g⁻¹ ^ r) v) = ν ^ r • Jacquet.mk ρ D.Nbar v)
    {c : ℝ} (hc : 0 < c)
    (hgrowth : ∀ ℓ : SmoothDual ρ, ∃ (C : ℝ) (k : ℕ), ∀ᶠ r : ℕ in atTop,
      ‖smoothDualPairing ρ ℓ (ρ (D.g⁻¹ ^ r) v)‖ ≤ C * c ^ r * (1 + r) ^ k) :
    ‖ν‖ ≤ c := by
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hA
  obtain ⟨x, hx⟩ : ∃ x, b x (Jacquet.mk ρ D.Nbar v) ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply hb.flip_injective hA
    ext x
    simp [h]
  obtain ⟨ℓ, rfl⟩ := Jacquet.mk_surjective (smoothContragredient ρ) D.N x
  obtain ⟨C, k, hCk⟩ := hgrowth ℓ
  obtain ⟨r₀, hr₀⟩ := hb.exists_pow_asymptotics hA v ℓ
  refine le_of_eventually_pow_mul_le hc (norm_pos_iff.mpr hx) (C := C) (k := k) ?_
  filter_upwards [hCk, eventually_ge_atTop r₀] with r hr hrr
  rw [hr₀ r hrr, hν r, map_smul, smul_eq_mul, norm_mul, norm_pow] at hr
  exact hr


/-- **Generalized eigenvalues of the normalized Jacquet action have modulus at most `1`**
(the step of Waldspurger's proof of Proposition III.2.2, (i) ⇒ (ii), that bounds `|χ(a)|`,
along the powers of one element). Let `ρ` be smooth with tempered coefficients for `Ξ ≥ 0` and
a nonnegative subadditive `σ`, let `M` normalize `Nbar` and `δ : M → ℝ>0` be the modulus
normalizing the Jacquet module. Let `m ∈ M` be such that there is `StablePairingData` with
opposite subgroup `Nbar` and contracting element `m⁻¹` satisfying `Admits`, and
`Ξ(mʳ) ≤ C δ(mʳ)^{1/2} (1 + σ(mʳ))^d` for `r ≥ 1`. If `y ≠ 0` is a generalized eigenvector of
the normalized action of `m` for the eigenvalue `μ`, then `|μ| ≤ 1`. -/
theorem norm_le_one_of_hasTemperedCoefficients (hρ : IsSmooth ρ) {Ξ σ : G → ℝ}
    (hT : HasTemperedCoefficients Ξ σ ρ) (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) {Nbar M : Subgroup G}
    (hMNbar : M ≤ Subgroup.normalizer Nbar) (δ : M →* ℝ≥0ˣ) (m : M)
    (hD : ∃ D : StablePairingData G, D.Nbar = Nbar ∧ D.g = (m : G)⁻¹ ∧ D.Admits ρ hρ)
    (hΞ : ∃ (C : ℝ) (d : ℕ), ∀ r : ℕ, 1 ≤ r →
      Ξ ((m : G) ^ r) ≤ C * NNReal.sqrt (δ (m ^ r) : ℝ≥0) * (1 + σ ((m : G) ^ r)) ^ d)
    {y : Coinvariants ρ Nbar} (hy : y ≠ 0) {μ : ℂ} {k : ℕ}
    (hk : ((normalizedActionOfModulus ρ Nbar M hMNbar δ m - μ • 1) ^ k) y = 0) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨D, hDN, hDg, hA⟩ := hD
  subst hDN
  set J := normalizedActionOfModulus ρ D.Nbar M hMNbar δ with hJ
  obtain ⟨w, hw0, hw⟩ := exists_apply_eq_smul_of_pow_apply_eq_zero (J m) _ hy hk
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ D.Nbar w
  set s : ℝ≥0 := NNReal.sqrt (δ m : ℝ≥0) with hs
  have hs0 : 0 < (s : ℝ) := by
    rw [hs, NNReal.coe_pos, NNReal.sqrt_pos]
    exact pos_iff_ne_zero.mpr (δ m).ne_zero
  have hsqrt_pow : ∀ r : ℕ, NNReal.sqrt (δ (m ^ r) : ℝ≥0) = s ^ r := by
    intro r
    rw [map_pow, Units.val_pow_eq_pow_val, hs]
    exact map_pow NNReal.sqrtHom _ r
  have hginv : ∀ r : ℕ, D.g⁻¹ ^ r = ((m ^ r : M) : G) := by
    intro r
    rw [hDg, inv_inv, Subgroup.coe_pow]
  have hJpow : ∀ r : ℕ, (J (m ^ r)) (Jacquet.mk ρ D.Nbar v) =
      μ ^ r • Jacquet.mk ρ D.Nbar v := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih, map_smul, hw, smul_smul, ← pow_succ]
  -- the eigenvalue of `m` on the unnormalized quotient
  have hν : ∀ r : ℕ, Jacquet.mk ρ D.Nbar (ρ (D.g⁻¹ ^ r) v) =
      ((s : ℂ) * μ) ^ r • Jacquet.mk ρ D.Nbar v := by
    intro r
    have e := normalizedActionOfModulus_mk ρ D.Nbar M hMNbar δ (m ^ r) v
    rw [← hJ, hJpow r, hsqrt_pow r] at e
    have hsr : ((s ^ r : ℝ≥0) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < ((s ^ r : ℝ≥0) : ℝ) := by rw [NNReal.coe_pow]; exact pow_pos hs0 r
      exact_mod_cast this.ne'
    rw [hginv r]
    have e' : Jacquet.mk ρ D.Nbar (ρ ((m ^ r : M) : G) v) =
        (((s ^ r : ℝ≥0) : ℝ) : ℂ) • (μ ^ r • Jacquet.mk ρ D.Nbar v) := by
      rw [e, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hsr), one_smul]
    rw [e', smul_smul, mul_pow]
    push_cast
    rfl
  have hbound : ‖(s : ℂ) * μ‖ ≤ s := by
    refine norm_le_of_stablePairing_eigenvector D hA hw0 hν hs0 fun ℓ => ?_
    obtain ⟨C₁, s₁, hC₁⟩ := hT v ℓ
    obtain ⟨C₂, d, hC₂⟩ := hΞ
    set g : G := (m : G) with hg
    set B : ℝ := 1 + σ 1 + σ g with hB
    have hB1 : 1 ≤ B := by linarith [hσ0 1, hσ0 g]
    refine ⟨|C₁| * |C₂| * B ^ d * B ^ |s₁|, d + ⌈|s₁|⌉₊, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hgr : D.g⁻¹ ^ r = g ^ r := by rw [hginv r, Subgroup.coe_pow]
    have hΞr : Ξ (g ^ r) ≤ |C₂| * (s : ℝ) ^ r * (1 + σ (g ^ r)) ^ d := by
      have h1 := hC₂ r hr
      rw [hsqrt_pow r, NNReal.coe_pow] at h1
      calc Ξ (g ^ r) ≤ C₂ * (s : ℝ) ^ r * (1 + σ (g ^ r)) ^ d := h1
        _ ≤ |C₂| * (s : ℝ) ^ r * (1 + σ (g ^ r)) ^ d := by
          gcongr
          · have := hσ0 (g ^ r)
            positivity
          · exact le_abs_self C₂
    have hpow_d : (1 + σ (g ^ r)) ^ d ≤ B ^ d * (1 + r) ^ d := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by linarith [hσ0 (g ^ r)])
      have h1 := le_add_nsmul_of_subadditive hσ g r
      have h2 := hσ0 g
      have h3 := hσ0 1
      have hn : (0 : ℝ) ≤ r := r.cast_nonneg
      nlinarith
    have hpow_s := one_add_rpow_le_of_subadditive hσ0 hσ g s₁ r
    rw [hgr]
    have hcoef := hC₁ (g ^ r)
    change ‖ℓ.val (ρ (g ^ r) v)‖ ≤ _
    have hy0 : 0 ≤ (1 + σ (g ^ r)) ^ s₁ := Real.rpow_nonneg (by linarith [hσ0 (g ^ r)]) _
    calc ‖ℓ.val (ρ (g ^ r) v)‖ ≤ C₁ * Ξ (g ^ r) * (1 + σ (g ^ r)) ^ s₁ := hcoef
      _ ≤ |C₁| * Ξ (g ^ r) * (1 + σ (g ^ r)) ^ s₁ := by
          gcongr
          · exact hΞ0 _
          · exact le_abs_self C₁
      _ ≤ |C₁| * (|C₂| * (s : ℝ) ^ r * (B ^ d * (1 + r) ^ d)) *
            (B ^ |s₁| * (1 + r) ^ ⌈|s₁|⌉₊) := by
          gcongr
          exact hΞr.trans (by gcongr)
      _ = |C₁| * |C₂| * B ^ d * B ^ |s₁| * (s : ℝ) ^ r * (1 + r) ^ (d + ⌈|s₁|⌉₊) := by
          ring
  rw [norm_mul, Complex.norm_of_nonneg (NNReal.coe_nonneg s)] at hbound
  exact (mul_le_iff_le_one_right hs0).mp hbound

/-- **Exponents are bounded by `1` on the open chamber.** In the setting of
`mem_closedPositiveCone_of_hasTemperedCoefficients` (pairing data `hD` and the bound `hΞ` on the
open chamber), a generalized eigenvalue `μ` of the normalized action of `j(a)` on the Jacquet
module, for `a` in the open chamber `{⟨α, H_M(a)⟩ > 0, α ∈ S}`, satisfies `|μ| ≤ 1`. -/
theorem norm_le_one_of_mem_openChamber (hρ : IsSmooth ρ) {Ξ σ : G → ℝ}
    (hT : HasTemperedCoefficients Ξ σ ρ) (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) {Nbar M : Subgroup G}
    (hMNbar : M ≤ Subgroup.normalizer Nbar) (δ : M →* ℝ≥0ˣ) {A : Type*} [CommGroup A]
    (j : A →* M) {E : Type*} [AddCommGroup E] [Module ℝ E]
    {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b) {S : Finset (Module.Dual ℝ E)}
    (hD : ∀ a, (∀ α ∈ S, 0 < α (HM a)) → ∃ D : StablePairingData G,
      D.Nbar = Nbar ∧ D.g = ((j a : M) : G)⁻¹ ∧ D.Admits ρ hρ)
    (hΞ : ∃ (C : ℝ) (d : ℕ), ∀ a, (∀ α ∈ S, 0 < α (HM a)) →
      Ξ (j a) ≤ C * NNReal.sqrt (δ (j a) : ℝ≥0) * (1 + σ (j a)) ^ d)
    {a : A} (ha : ∀ α ∈ S, 0 < α (HM a)) {y : Coinvariants ρ Nbar} (hy : y ≠ 0) {μ : ℂ}
    {k : ℕ} (hk : ((normalizedActionOfModulus ρ Nbar M hMNbar δ (j a) - μ • 1) ^ k) y = 0) :
    ‖μ‖ ≤ 1 := by
  refine norm_le_one_of_hasTemperedCoefficients hρ hT hΞ0 hσ0 hσ hMNbar δ (j a) (hD a ha) ?_
    hy hk
  obtain ⟨C, d, hC⟩ := hΞ
  refine ⟨C, d, fun r hr => ?_⟩
  have har : ∀ α ∈ S, 0 < α (HM (a ^ r)) := by
    intro α hα
    have h1 : HM 1 = 0 := by
      have e := hHM 1 1
      rw [mul_one] at e
      calc HM 1 = HM 1 + HM 1 - HM 1 := by abel
        _ = 0 := by rw [← e, sub_self]
    have e : ∀ n : ℕ, HM (a ^ n) = (n : ℝ) • HM a := by
      intro n
      induction n with
      | zero => rw [pow_zero, h1, Nat.cast_zero, zero_smul]
      | succ n ih => rw [pow_succ, hHM, ih, Nat.cast_succ, add_smul, one_smul]
    rw [e, map_smul, smul_eq_mul]
    exact mul_pos (Nat.cast_pos.mpr (by omega)) (ha α hα)
  have h := hC (a ^ r) har
  rwa [map_pow, Subgroup.coe_pow] at h

/-- **Waldspurger, Proposition III.2.2, (i) ⇒ (ii), abstract form.** Let `ρ` be smooth with
tempered coefficients for `Ξ ≥ 0` and a nonnegative subadditive `σ`, let `M` normalize
`Nbar` (the unipotent radical `U` of `P`) and `δ : M → ℝ>0` be the modulus normalizing the
Jacquet module, and let `j : A →* M` and `H_M : A → E` be as in
`mem_closedPositiveCone_of_norm_le_one`. Assume:

* for every `a` in the open chamber `{⟨α, H_M(a)⟩ > 0, α ∈ S}` there is
  `StablePairingData` with opposite subgroup `Nbar` and contracting element `j(a)⁻¹`
  satisfying `Admits`;
* `Ξ(j(a)) ≤ C δ(j(a))^{1/2} (1 + σ(j(a)))^d` on the open chamber (Lemme II.1.1);
* `y ≠ 0` lies in the generalized eigenspace of the normalized action of each `j(a)` on
  the Jacquet module for the eigenvalue `χ(a)` (an exponent `χ`), with
  `|χ(a)| = q^{-⟨λ, H_M(a)⟩}`, `q > 1`.

Then `λ = Re(χ)` lies in `closedPositiveCone S`. -/
theorem mem_closedPositiveCone_of_hasTemperedCoefficients (hρ : IsSmooth ρ) {Ξ σ : G → ℝ}
    (hT : HasTemperedCoefficients Ξ σ ρ) (hΞ0 : ∀ g, 0 ≤ Ξ g) (hσ0 : ∀ g, 0 ≤ σ g)
    (hσ : ∀ g h, σ (g * h) ≤ σ g + σ h) {Nbar M : Subgroup G}
    (hMNbar : M ≤ Subgroup.normalizer Nbar) (δ : M →* ℝ≥0ˣ) {A : Type*} [CommGroup A]
    (j : A →* M) {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {HM : A → E} (hHM : ∀ a b, HM (a * b) = HM a + HM b)
    (hspan : Submodule.span ℝ (Set.range HM) = ⊤) {S : Finset (Module.Dual ℝ E)}
    (hS : LinearIndependent ℝ ((↑) : S → Module.Dual ℝ E)) {a₀ : A}
    (ha₀ : ∀ α ∈ S, 0 < α (HM a₀))
    (hD : ∀ a, (∀ α ∈ S, 0 < α (HM a)) → ∃ D : StablePairingData G,
      D.Nbar = Nbar ∧ D.g = ((j a : M) : G)⁻¹ ∧ D.Admits ρ hρ)
    (hΞ : ∃ (C : ℝ) (d : ℕ), ∀ a, (∀ α ∈ S, 0 < α (HM a)) →
      Ξ (j a) ≤ C * NNReal.sqrt (δ (j a) : ℝ≥0) * (1 + σ (j a)) ^ d)
    {χ : A →* ℂˣ} {y : Coinvariants ρ Nbar} (hy : y ≠ 0)
    (hχ : ∀ a, ∃ k : ℕ,
      ((normalizedActionOfModulus ρ Nbar M hMNbar δ (j a) - (χ a : ℂ) • 1) ^ k) y = 0)
    {q : ℝ} (hq : 1 < q) {lam : Module.Dual ℝ E}
    (hlam : ∀ a, ‖(χ a : ℂ)‖ = q ^ (-lam (HM a))) :
    lam ∈ closedPositiveCone S := by
  refine mem_closedPositiveCone_of_norm_le_one hHM hspan hS ha₀ hq hlam fun a ha => ?_
  obtain ⟨k, hk⟩ := hχ a
  exact norm_le_one_of_mem_openChamber hρ hT hΞ0 hσ0 hσ hMNbar δ j hHM hD hΞ ha hy hk

end StablePairing

end Langlands.HarishChandraSchwartz
