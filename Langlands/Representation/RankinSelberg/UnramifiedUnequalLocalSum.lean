import Langlands.Representation.RankinSelberg.UnramifiedPairTorusCoefficient
import Langlands.Representation.RankinSelberg.SchurCauchyEvaluation
import Langlands.Representation.RankinSelberg.SymmetricDominant
import Langlands.Representation.RankinSelberg.JacobiTrudiPadding
import Langlands.Representation.Whittaker.Spherical

/-! # The unramified unequal-rank local sum

For Satake parameters `a` of `GL_(r+1)` and `b` of `GL_(t+1)` with `t < r`, the sum over the
torus weights `λ` of `GL_(t+1)` of
`δ_B⁻¹(ϖ^λ) · W°_a(diag(ϖ^λ, 1_(r-t))) · W°_b(ϖ^λ) · |det ϖ^λ|^(s - (r-t)/2)`
is the local pair factor `∏_(i,j) (1 - a_i b_j q^(-s))⁻¹`, with uniform half-plane of absolute
convergence under polynomial bounds `q^A`, `q^B` on the parameters. See the paired Markdown.
-/

noncomputable section
open Langlands.GeneralLinear Langlands.GeneralLinear.Spherical Langlands.GeneralLinear.Iwasawa
  Langlands.Whittaker
set_option autoImplicit false

namespace Langlands.RankinSelberg.UnramifiedUnequalLocalSum

/-! ### Zero padding of weights -/

/-- The weight of `diag(ϖ^λ, 1_(r-t))`: a weight `λ` of `GL_(t+1)` extended by zeros to a
weight of `GL_(r+1)`. -/
def padZeroWeight {t : ℕ} (r : ℕ) (lam : Fin (t + 1) → ℤ) : Fin (r + 1) → ℤ :=
  fun i => if h : (i : ℕ) < t + 1 then lam ⟨i, h⟩ else 0

theorem padZeroWeight_of_lt {t r : ℕ} (lam : Fin (t + 1) → ℤ) (i : Fin (r + 1))
    (h : (i : ℕ) < t + 1) : padZeroWeight r lam i = lam ⟨i, h⟩ :=
  dite_eq_left h

theorem padZeroWeight_of_le {t r : ℕ} (lam : Fin (t + 1) → ℤ) (i : Fin (r + 1))
    (h : t + 1 ≤ (i : ℕ)) : padZeroWeight r lam i = 0 :=
  dite_eq_right (by omega)

theorem antitone_padZeroWeight {t : ℕ} (r : ℕ) {lam : Fin (t + 1) → ℤ} (hlam : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) : Antitone (padZeroWeight r lam) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  by_cases hj : (j : ℕ) < t + 1
  · have hi : (i : ℕ) < t + 1 := by omega
    rw [padZeroWeight_of_lt lam i hi, padZeroWeight_of_lt lam j hj]
    exact hlam (Fin.mk_le_mk.mpr hij')
  · rw [padZeroWeight_of_le lam j (by omega)]
    by_cases hi : (i : ℕ) < t + 1
    · rw [padZeroWeight_of_lt lam i hi]
      exact hpos _
    · rw [padZeroWeight_of_le lam i (by omega)]

/-- If the padded weight is antitone (and at least one zero is appended), the weight is a
partition: antitone with nonnegative entries. -/
theorem antitone_nonneg_of_antitone_padZeroWeight {t r : ℕ} (h : t < r)
    {lam : Fin (t + 1) → ℤ} (hA : Antitone (padZeroWeight r lam)) :
    Antitone lam ∧ ∀ i, 0 ≤ lam i := by
  have hval (i : Fin (t + 1)) :
      padZeroWeight r lam ⟨i, by omega⟩ = lam i := padZeroWeight_of_lt lam _ i.isLt
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [← hval i, ← hval j]
    exact hA (Fin.mk_le_mk.mpr hij)
  · have hz : padZeroWeight r lam ⟨t + 1, by omega⟩ = 0 := padZeroWeight_of_le lam _ le_rfl
    rw [← hval i, ← hz]
    exact hA (Fin.mk_le_mk.mpr (by omega))

theorem sum_mul_padZeroWeight {t r : ℕ} (h : t ≤ r) (c : ℕ → ℤ) (lam : Fin (t + 1) → ℤ) :
    ∑ i : Fin (r + 1), c i * padZeroWeight r lam i = ∑ i : Fin (t + 1), c i * lam i := by
  let g : ℕ → ℤ := fun m => c m * if h : m < t + 1 then lam ⟨m, h⟩ else 0
  have h1 : ∑ i : Fin (r + 1), c i * padZeroWeight r lam i =
      ∑ m ∈ Finset.range (r + 1), g m :=
    Fin.sum_univ_eq_sum_range g (r + 1)
  have h2 : ∑ i : Fin (t + 1), c i * lam i = ∑ m ∈ Finset.range (t + 1), g m := by
    rw [← Fin.sum_univ_eq_sum_range g (t + 1)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [g, dite_eq_left i.isLt]
  rw [h1, h2]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro m _ hm
  have : ¬ m < t + 1 := by simpa using hm
  simp only [g, dite_eq_right this, mul_zero]

/-- The half-modulus exponent of the padded weight. -/
theorem sum_halfModulus_padZeroWeight {t r : ℕ} (h : t ≤ r) (lam : Fin (t + 1) → ℤ) :
    ∑ i : Fin (r + 1), ((r : ℤ) - 2 * (i : ℤ)) * padZeroWeight r lam i =
      ∑ i : Fin (t + 1), ((t : ℤ) - 2 * (i : ℤ)) * lam i +
        ((r - t : ℕ) : ℤ) * ∑ i, lam i := by
  refine (sum_mul_padZeroWeight h (fun m => (r : ℤ) - 2 * (m : ℤ)) lam).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub h]
  ring

/-! ### Schur values of natural partitions -/

/-- The Schur value of the padded natural partition is the Jacobi–Trudi value of the
partition itself in the `r + 1` parameters. -/
theorem satakeSchur_padZeroWeight {t r : ℕ} (h : t ≤ r) (a : Fin (r + 1) → ℂˣ)
    (α : Fin (t + 1) → ℕ) (hα : Antitone α) :
    satakeSchur a (padZeroWeight r fun i => (α i : ℤ)) =
      jacobiTrudiValue (fun i => (a i : ℂ)) α := by
  have hA : Antitone (padZeroWeight r fun i => (α i : ℤ)) :=
    antitone_padZeroWeight r (fun i j hij => Nat.cast_le.mpr (hα hij)) (fun i => Nat.cast_nonneg _)
  have hpos : ∀ i, 0 ≤ padZeroWeight r (fun i => (α i : ℤ)) i := by
    intro i
    unfold padZeroWeight
    split_ifs
    · positivity
    · exact le_rfl
  rw [satakeSchur_eq_eval_jacobiTrudi a _ hA hpos, jacobiTrudi_eq_jacobiTrudiIn]
  unfold jacobiTrudiValue
  congr 1
  rw [← jacobiTrudiIn_padWeight (Fin (r + 1)) ℂ (fun i => (α i : ℤ)) (r - t)]
  refine UnramifiedPairTorus.jacobiTrudiIn_cast (Fin (r + 1)) ℂ (by omega) _ _ (fun i => ?_)
  rw [UnramifiedPairTorus.padWeight_apply]
  simp only [Fin.val_cast]
  rfl

/-- The Schur value of a natural partition is its Jacobi–Trudi value. -/
theorem satakeSchur_natWeight' {t : ℕ} (b : Fin (t + 1) → ℂˣ) (α : Fin (t + 1) → ℕ)
    (hα : Antitone α) :
    satakeSchur b (fun i => (α i : ℤ)) = jacobiTrudiValue (fun i => (b i : ℂ)) α := by
  rw [satakeSchur_eq_eval_jacobiTrudi b _ (fun i j hij => Nat.cast_le.mpr (hα hij))
    (fun i => Nat.cast_nonneg _)]
  rfl

/-! ### The local term -/

/-- The term of weight `λ` of the unramified unequal-rank local sum:
`δ_B⁻¹(ϖ^λ) · W°_a(diag(ϖ^λ, 1_(r-t))) · W°_b(ϖ^λ) · |det ϖ^λ|^(s - (r-t)/2)`, with
`δ_B⁻¹(ϖ^λ) = q^(∑_i (t - 2i) λ_i)`, the torus values of the spherical Whittaker functions
written out (`δ^(1/2) · s_λ` on dominant weights, `0` otherwise), and
`|det ϖ^λ| = q^(-∑_i λ_i)`. -/
def localTerm (q : ℕ) {r t : ℕ} (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ) (s : ℂ)
    (lam : Fin (t + 1) → ℤ) : ℂ :=
  (((q : ℝ) ^ (∑ i : Fin (t + 1), ((t : ℤ) - 2 * (i : ℤ)) * lam i) : ℝ) : ℂ) *
    ((if Antitone (padZeroWeight r lam) then
        halfModulus q (padZeroWeight r lam) * satakeSchur a (padZeroWeight r lam) else 0) *
      (if Antitone lam then halfModulus q lam * satakeSchur b lam else 0) *
      Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) *
        (Real.log ((q : ℝ) ^ (-(∑ i, lam i))) : ℂ)))

/-- The local term in terms of the explicit spherical Whittaker functions of `GL_(r+1)(F)` and
`GL_(t+1)(F)` at torus elements, over any valued field with uniformizer `ϖ` and any integrally
trivial characters. -/
theorem localTerm_eq_sphericalWhittaker {F : Type*} [Field F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀} {ϖ : Fˣ}
    (hϖ : IsUniformizingElement v ϖ) {r t : ℕ} {θ : upperUnipotent (r + 1) F →* ℂˣ}
    {θ' : upperUnipotent (t + 1) F →* ℂˣ} (hθ : IsIntegrallyTrivial v θ)
    (hθ' : IsIntegrallyTrivial v θ') (q : ℕ) (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ)
    (s : ℂ) (lam : Fin (t + 1) → ℤ) :
    localTerm q a b s lam =
      (((q : ℝ) ^ (∑ i : Fin (t + 1), ((t : ℤ) - 2 * (i : ℤ)) * lam i) : ℝ) : ℂ) *
        (sphericalWhittaker hϖ θ q a (torus ϖ (padZeroWeight r lam)) *
          sphericalWhittaker hϖ θ' q b (torus ϖ lam) *
          Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) *
            (Real.log ((q : ℝ) ^ (-(∑ i, lam i))) : ℂ))) := by
  rw [sphericalWhittaker_torus hϖ q a hθ, sphericalWhittaker_torus hϖ q b hθ']
  rfl

/-- The scalar factors of a local term combine to `q^(-s|λ|)`. -/
theorem scalar_identity (q : ℕ) (hq : 0 < q) (d : ℕ) (A : ℤ) (S : ℕ) (s : ℂ) :
    (((q : ℝ) ^ A : ℝ) : ℂ) *
        (((Real.sqrt q : ℝ) : ℂ) ^ (-(A + (d : ℤ) * (S : ℤ))) * ((Real.sqrt q : ℝ) : ℂ) ^ (-A)) *
        Complex.exp ((s - (d : ℂ) / 2) * (Real.log ((q : ℝ) ^ (-(S : ℤ))) : ℂ)) =
      ((q : ℂ) ^ (-s)) ^ S := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : ((Real.sqrt q : ℝ) : ℂ) = Complex.exp ((Real.log q : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq', Complex.ofReal_exp]
    push_cast
    ring_nf
  have hqa : (((q : ℝ) ^ A : ℝ) : ℂ) = Complex.exp (A * (Real.log q : ℂ)) := by
    rw [Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hq']
    norm_cast
  have hlog : Real.log ((q : ℝ) ^ (-(S : ℤ))) = -(S : ℝ) * Real.log q := by
    rw [Real.log_zpow]
    push_cast
    ring
  have hqs : (q : ℂ) ^ (-s) = Complex.exp ((Real.log q : ℂ) * (-s)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq'.ne'), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hq'.le]
  rw [hqa, hsq, hlog, hqs, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- On a natural partition `α` the local term is the Schur pair term
`s_α(a) s_α(b) (q^(-s))^|α|`. -/
theorem localTerm_natWeight {q : ℕ} (hq : 0 < q) {r t : ℕ} (h : t < r)
    (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ) (s : ℂ) (α : Fin (t + 1) → ℕ)
    (hα : Antitone α) :
    localTerm q a b s (fun i => (α i : ℤ)) =
      schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) ((q : ℂ) ^ (-s)) α := by
  have hα' : Antitone (fun i => (α i : ℤ)) := fun i j hij => Nat.cast_le.mpr (hα hij)
  have hA : Antitone (padZeroWeight r fun i => (α i : ℤ)) :=
    antitone_padZeroWeight r hα' (fun i => Nat.cast_nonneg _)
  unfold localTerm
  rw [ite_eq_left hA, ite_eq_left hα', satakeSchur_padZeroWeight h.le a α hα,
    satakeSchur_natWeight' b α hα]
  unfold halfModulus schurPairTerm
  rw [sum_halfModulus_padZeroWeight h.le]
  have hS : (∑ i, (α i : ℤ)) = ((∑ i, α i : ℕ) : ℤ) := by push_cast; rfl
  rw [hS]
  have key := scalar_identity q hq (r - t) (∑ i : Fin (t + 1), ((t : ℤ) - 2 * (i : ℤ)) * (α i : ℤ))
    (∑ i, α i) s
  push_cast at key ⊢
  linear_combination (jacobiTrudiValue (fun i => (a i : ℂ)) α *
    jacobiTrudiValue (fun j => (b j : ℂ)) α) * key

/-! ### The Cauchy identity with an explicit radius -/

/-- An explicit exponential bound on Jacobi–Trudi values in terms of `completeGrowthRate`. -/
theorem norm_jacobiTrudiValue_le_rate {σ : Type*} [Fintype σ] [DecidableEq σ] (m : ℕ)
    (x : σ → ℂ) (α : Fin m → ℕ) :
    ‖jacobiTrudiValue x α‖ ≤
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) * completeGrowthConstant x ^ m *
        (completeGrowthRate x ^ m) ^ m) * (completeGrowthRate x ^ m) ^ (∑ i, α i) := by
  refine (norm_jacobiTrudiValue_le x α).trans_eq ?_
  have hpow : (completeGrowthRate x ^ (∑ i, α i)) ^ m =
      (completeGrowthRate x ^ m) ^ (∑ i, α i) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  simp only [pow_add, mul_pow]
  rw [hpow]
  ring

/-- If `R_x^(n+1) R_y^(n+1) ‖X‖ < 1` for the growth rates `R = 1 + ∑ ‖·‖`, the Schur pair
series over partitions with at most `n + 1` parts converges absolutely to
`∏_(i,j) (1 - x_i y_j X)⁻¹`. -/
theorem hasSum_schurPairTerm_of_growth {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
    (x : σ → ℂ) (y : Fin (n + 1) → ℂ) (X : ℂ)
    (hX : completeGrowthRate x ^ (n + 1) * completeGrowthRate y ^ (n + 1) * ‖X‖ < 1) :
    Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} => ‖schurPairTerm x y X α.val‖) ∧
      HasSum (fun α : {α : Fin (n + 1) → ℕ // Antitone α} => schurPairTerm x y X α.val)
        (∏ j : Fin (n + 1), ∏ i : σ, (1 - x i * y j * X))⁻¹ := by
  have hrx := completeGrowthRate_ge_one x
  have hry := completeGrowthRate_ge_one y
  have hall := summable_norm_schurPairTerm_of_bounds (m := n + 1) x y _ _ _ _
    (by have := completeGrowthConstant_pos x; positivity) (one_le_pow₀ hrx)
    (by have := completeGrowthConstant_pos y; positivity) (one_le_pow₀ hry)
    (norm_jacobiTrudiValue_le_rate (n + 1) x) (norm_jacobiTrudiValue_le_rate (n + 1) y) X hX
  have hsum : Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} =>
      ‖schurPairTerm x y X α.val‖) := hall.subtype _
  have hnorm_le (z : σ → ℂ) (i : σ) : ‖z i‖ ≤ completeGrowthRate z := by
    have := Finset.single_le_sum (fun j _ => norm_nonneg (z j)) (Finset.mem_univ i)
    unfold completeGrowthRate
    linarith
  have hnorm_le' (z : Fin (n + 1) → ℂ) (j : Fin (n + 1)) : ‖z j‖ ≤ completeGrowthRate z := by
    have := Finset.single_le_sum (fun i _ => norm_nonneg (z i)) (Finset.mem_univ j)
    unfold completeGrowthRate
    linarith
  have hpair (i : σ) (j : Fin (n + 1)) : ‖x i * y j * X‖ < 1 := by
    rw [norm_mul, norm_mul]
    have h1 : ‖x i‖ ≤ completeGrowthRate x ^ (n + 1) :=
      (hnorm_le x i).trans (le_self_pow₀ hrx (Nat.succ_ne_zero n))
    have h2 : ‖y j‖ ≤ completeGrowthRate y ^ (n + 1) :=
      (hnorm_le' y j).trans (le_self_pow₀ hry (Nat.succ_ne_zero n))
    calc ‖x i‖ * ‖y j‖ * ‖X‖
        ≤ completeGrowthRate x ^ (n + 1) * completeGrowthRate y ^ (n + 1) * ‖X‖ := by
          gcongr
      _ < 1 := hX
  refine ⟨hsum, ?_⟩
  have hval := (tsum_schurPairTerm_eq_seriesValue x y X hsum).trans
    (seriesValue_complexCauchySeries x y X hpair)
  rw [← hval]
  exact hsum.of_norm.hasSum

/-! ### The local sum -/

/-- **The unramified unequal-rank local sum.** If `R_a^(t+1) R_b^(t+1) ‖q^(-s)‖ < 1` for the
growth rates `R = 1 + ∑ ‖·‖` of the parameters, the local terms over all weights
`λ : Fin (t+1) → ℤ` are absolutely summable with sum `∏_(i,j) (1 - a_i b_j q^(-s))⁻¹`. -/
theorem hasSum_localTerm_of_growth {q : ℕ} (hq : 0 < q) {r t : ℕ} (h : t < r)
    (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ) (s : ℂ)
    (hX : completeGrowthRate (fun i => (a i : ℂ)) ^ (t + 1) *
      completeGrowthRate (fun j => (b j : ℂ)) ^ (t + 1) * ‖(q : ℂ) ^ (-s)‖ < 1) :
    Summable (fun lam => ‖localTerm q a b s lam‖) ∧
      HasSum (localTerm q a b s)
        (∏ i : Fin (r + 1), ∏ j : Fin (t + 1), (1 - (a i : ℂ) * b j * (q : ℂ) ^ (-s)))⁻¹ := by
  obtain ⟨hsum, hhas⟩ := hasSum_schurPairTerm_of_growth (fun i => (a i : ℂ))
    (fun j => (b j : ℂ)) ((q : ℂ) ^ (-s)) hX
  let ι : {α : Fin (t + 1) → ℕ // Antitone α} → (Fin (t + 1) → ℤ) :=
    fun α i => (α.val i : ℤ)
  have hι : Function.Injective ι := by
    intro α β hαβ
    apply Subtype.ext
    funext i
    have h1 : ((α.val i : ℕ) : ℤ) = (β.val i : ℤ) := congrFun hαβ i
    exact Int.ofNat_inj.mp h1
  have hsupp : ∀ lam, lam ∉ Set.range ι → localTerm q a b s lam = 0 := by
    intro lam hlam
    by_contra hne
    have hA : Antitone (padZeroWeight r lam) := by
      by_contra hA
      apply hne
      unfold localTerm
      rw [ite_eq_right hA]
      simp
    obtain ⟨hanti, hpos⟩ := antitone_nonneg_of_antitone_padZeroWeight h hA
    refine hlam ⟨⟨fun i => (lam i).toNat, fun i j hij => Int.toNat_le_toNat (hanti hij)⟩, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hpos i)
  have hcomp : localTerm q a b s ∘ ι =
      fun α : {α : Fin (t + 1) → ℕ // Antitone α} =>
        schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) ((q : ℂ) ^ (-s)) α.val := by
    funext α
    exact localTerm_natWeight hq h a b s α.val α.property
  have hprod : (∏ i : Fin (r + 1), ∏ j : Fin (t + 1), (1 - (a i : ℂ) * b j * (q : ℂ) ^ (-s))) =
      ∏ j : Fin (t + 1), ∏ i : Fin (r + 1), (1 - (a i : ℂ) * b j * (q : ℂ) ^ (-s)) :=
    Finset.prod_comm
  refine ⟨?_, ?_⟩
  · have hsupp' : ∀ lam, lam ∉ Set.range ι → ‖localTerm q a b s lam‖ = 0 := fun lam hlam => by
      rw [hsupp lam hlam, norm_zero]
    rw [← hι.summable_iff hsupp']
    have : (fun lam => ‖localTerm q a b s lam‖) ∘ ι =
        fun α : {α : Fin (t + 1) → ℕ // Antitone α} =>
          ‖schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) ((q : ℂ) ^ (-s)) α.val‖ := by
      funext α
      exact congrArg norm (congrFun hcomp α)
    rw [this]
    exact hsum
  · rw [← hι.hasSum_iff hsupp, hcomp, hprod]
    exact hhas

/-- **Uniform half-plane.** For bounds `‖a_i‖ ≤ q^A` and `‖b_j‖ ≤ q^B`, there is `σ`,
depending only on `r`, `t`, `A`, `B`, such that for every `q ≥ 2` and every `s` with
`σ < Re s` the local terms are absolutely summable with sum
`∏_(i,j) (1 - a_i b_j q^(-s))⁻¹`. -/
theorem exists_hasSum_localTerm {r t : ℕ} (h : t < r) (A B : ℝ) :
    ∃ σ : ℝ, ∀ q : ℕ, 1 < q → ∀ (a : Fin (r + 1) → ℂˣ) (b : Fin (t + 1) → ℂˣ),
      (∀ i, ‖(a i : ℂ)‖ ≤ (q : ℝ) ^ A) → (∀ j, ‖(b j : ℂ)‖ ≤ (q : ℝ) ^ B) →
      ∀ s : ℂ, σ < s.re →
        Summable (fun lam => ‖localTerm q a b s lam‖) ∧
          HasSum (localTerm q a b s)
            (∏ i : Fin (r + 1), ∏ j : Fin (t + 1), (1 - (a i : ℂ) * b j * (q : ℂ) ^ (-s)))⁻¹ := by
  set m : ℕ := t + 1
  set A' : ℝ := max A 0
  set B' : ℝ := max B 0
  set K : ℝ := (((r : ℝ) + 2) * ((t : ℝ) + 2)) ^ m
  have hK1 : 1 ≤ K := one_le_pow₀ (by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r),
    (Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(m : ℝ) * (A' + B') + Real.log K / Real.log 2, fun q hq a b ha hb s hs => ?_⟩
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  set L : ℝ := Real.log q
  have hLpos : 0 < L := lt_of_lt_of_le hlog2 hL
  -- growth rate bounds
  have hrate {k : ℕ} (z : Fin (k + 1) → ℂˣ) (C : ℝ) (hz : ∀ i, ‖(z i : ℂ)‖ ≤ (q : ℝ) ^ C) :
      completeGrowthRate (fun i => (z i : ℂ)) ≤ ((k : ℝ) + 2) * Real.exp (max C 0 * L) := by
    have hE : 1 ≤ Real.exp (max C 0 * L) :=
      Real.one_le_exp (mul_nonneg (le_max_right _ _) hLpos.le)
    have hzi (i : Fin (k + 1)) : ‖(z i : ℂ)‖ ≤ Real.exp (max C 0 * L) := by
      refine (hz i).trans ?_
      rw [Real.rpow_def_of_pos (by linarith), mul_comm]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos.le)
    have hs : ∑ i, ‖(z i : ℂ)‖ ≤ ((k : ℝ) + 1) * Real.exp (max C 0 * L) := by
      calc ∑ i, ‖(z i : ℂ)‖ ≤ ∑ _i : Fin (k + 1), Real.exp (max C 0 * L) :=
            Finset.sum_le_sum fun i _ => hzi i
        _ = ((k : ℝ) + 1) * Real.exp (max C 0 * L) := by simp
    unfold completeGrowthRate
    nlinarith
  refine hasSum_localTerm_of_growth hq0 h a b s ?_
  have hra := hrate a A ha
  have hrb := hrate b B hb
  have hnorm : ‖(q : ℂ) ^ (-s)‖ = Real.exp (-s.re * L) := by
    rw [Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re,
      Real.rpow_def_of_pos (by linarith), mul_comm]
  rw [hnorm]
  have hra0 : 0 ≤ completeGrowthRate (fun i => (a i : ℂ)) :=
    (completeGrowthRate_pos _).le
  have hrb0 : 0 ≤ completeGrowthRate (fun j => (b j : ℂ)) :=
    (completeGrowthRate_pos _).le
  calc completeGrowthRate (fun i => (a i : ℂ)) ^ (t + 1) *
        completeGrowthRate (fun j => (b j : ℂ)) ^ (t + 1) * Real.exp (-s.re * L)
      ≤ (((r : ℝ) + 2) * Real.exp (A' * L)) ^ m * (((t : ℝ) + 2) * Real.exp (B' * L)) ^ m *
          Real.exp (-s.re * L) := by
        gcongr
    _ = Real.exp (Real.log K + ((m : ℝ) * (A' + B') - s.re) * L) := by
        rw [Real.exp_add, Real.exp_log hK0, mul_pow, mul_pow, ← Real.exp_nat_mul,
          ← Real.exp_nat_mul]
        simp only [K, mul_pow]
        rw [show ((m : ℝ) * (A' + B') - s.re) * L =
          (m : ℝ) * (A' * L) + (m : ℝ) * (B' * L) + -s.re * L by ring, Real.exp_add,
          Real.exp_add]
        ring
    _ < 1 := by
        refine lt_of_lt_of_eq (Real.exp_lt_exp.mpr ?_) Real.exp_zero
        have hu : Real.log K / Real.log 2 < s.re - (m : ℝ) * (A' + B') := by linarith
        have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
        have hu0 : 0 < s.re - (m : ℝ) * (A' + B') :=
          lt_of_le_of_lt (div_nonneg hlogK hlog2.le) hu
        have h1 : Real.log K < (s.re - (m : ℝ) * (A' + B')) * Real.log 2 :=
          (div_lt_iff₀ hlog2).mp hu
        have h2 : (s.re - (m : ℝ) * (A' + B')) * Real.log 2 ≤
            (s.re - (m : ℝ) * (A' + B')) * L := mul_le_mul_of_nonneg_left hL hu0.le
        nlinarith

end Langlands.RankinSelberg.UnramifiedUnequalLocalSum
