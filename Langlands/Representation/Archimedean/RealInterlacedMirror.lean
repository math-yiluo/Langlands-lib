import Langlands.Representation.Archimedean.RealInterlacedProof

/-!
# The linked Jacquet functional for two interlaced induction blocks: the mirror case

The chain of multipliers in the case `|m(d)| < |m(e)|` (that is `C > A`), and the proof of
`RealInterlacedInducedInducedLinkedJacquetFunctionalStatement` from the two cases. With the
separated case this proves `RealInducedInducedLinkedJacquetFunctionalStatement` (II).
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInterlacedJacquet

open Langlands.LocalFactor.Archimedean
open RealJacquetFrobenius RealBlockJacquet RealBlockMultiplier RealBlockRotation
  RealBlockFourierFinite RealBlockDerivative RealCharacterCrossing RealBlockFlatJacquet InductionStages GramFormula


/-! ## The case `C > A` -/

section CA

/-- The first column `e₂` of the test functions for `C > A`. -/
def vA : Fin 4 → ℂ := ![0, 0, 1, 0]

/-- The second column `-e₀ + i e₁ + e₃` of the test functions for `C > A`. -/
def vB : Fin 4 → ℂ := ![-1, Complex.I, 0, 1]

theorem colv_vA_one : colv vA 0 1 = 0 ∧ colv vA 1 1 = 0 ∧ colv vA 2 1 = 1 ∧ colv vA 3 1 = 0 := by
  simp [colv_one, vA]

theorem w_one_CA : w1 vA vB 1 = 1 ∧ w2 vA vB 1 = 1 ∧ w3 vA vB 1 = -Complex.I := by
  simp [w1, w2, w3, pl, colv_one, vA, vB]

/-- Values along `r₁(t) r₂(π/2)`. -/
theorem values_CA_kappa (t : ℝ) :
    yZ h42 vA ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 2 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) = Complex.I ∧
      yZb h42 vA ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 2 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) = -Complex.I ∧
      nup vA vB ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 2 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) =
          Complex.I * expMode (-1) t + Complex.I ∧
      num vA vB ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 2 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)) =
          Complex.I * expMode (-1) t + -Complex.I := by
  obtain ⟨-, -, a2, a3⟩ := colv_rot1 vA t
    ((blockRotation 4 2 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)
  obtain ⟨-, b1, b2, b3⟩ := colv_rot2 vA (Real.pi / 2) 1
  obtain ⟨-, c2, c3⟩ := w_rot1 vA vB t
    ((blockRotation 4 2 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1)
  obtain ⟨d1, d2, d3⟩ := w_rot2 vA vB (Real.pi / 2) 1
  obtain ⟨-, o1, o2, o3⟩ := colv_vA_one
  obtain ⟨p1, p2, p3⟩ := w_one_CA
  simp only [yZ2_apply, yZb2_apply, nup, num, a2, a3, b1, b2, b3, c2, c3, d1, d2, d3, o1, o2,
    o3, p1, p2, p3, Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero,
    Complex.ofReal_one, expMode_neg_one_eq]
  refine ⟨by ring, by ring, ?_, ?_⟩
  · linear_combination (Real.sin t : ℂ) * Complex.I_sq
  · linear_combination (Real.sin t : ℂ) * Complex.I_sq

/-- Values along `r₀(θ)` and `s₃ s₂ r₀(θ)`. -/
theorem values_CA_rot0 (r m : ℕ) (θ : ℝ) :
    (yZ h41 vA ^ r * wp vA vB ^ m) (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ) =
        Complex.I ^ r * (Complex.I * expMode 1 θ + 1) ^ m ∧
      (yZ h41 vA ^ r * wp vA vB ^ m)
          (fl 3 * (fl 2 * (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ))) =
        (-Complex.I) ^ r * (-Complex.I * expMode 1 θ + 1) ^ m := by
  set R : Matrix (Fin 4) (Fin 4) ℝ := (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ) with hR
  have e : R = (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ) * 1 := (mul_one _).symm
  obtain ⟨-, a1, a2, -⟩ := colv_rot0 vA θ 1
  obtain ⟨b1, b2, -⟩ := w_rot0 vA vB θ 1
  obtain ⟨o0, o1, o2, -⟩ := colv_vA_one
  obtain ⟨p1, p2, p3⟩ := w_one_CA
  obtain ⟨f1, f2, -⟩ := w_fl32 vA vB R
  have hy : yZ h41 vA R = Complex.I := by
    rw [yZ1_apply, e, a1, a2, o0, o1, o2]
    ring
  have hy' : yZ h41 vA (fl 3 * (fl 2 * R)) = -Complex.I := by
    rw [yZ1_fl32, e, a1, a2, o0, o1, o2]
    ring
  have hw1 : w1 vA vB R = 1 := by rw [e, b1, p1]
  have hw2 : w2 vA vB R = expMode 1 θ := by
    rw [e, b2, p2, p3, expMode_one_eq]
    ring
  have hw : wp vA vB R = Complex.I * expMode 1 θ + 1 := by
    rw [wp_apply, hw1, hw2]
    ring
  have hw' : wp vA vB (fl 3 * (fl 2 * R)) = -Complex.I * expMode 1 θ + 1 := by
    rw [wp_apply, f1, f2, hw1, hw2]
    ring
  constructor
  · simp only [Pi.mul_apply, Pi.pow_apply, hy, hw]
  · simp only [Pi.mul_apply, Pi.pow_apply, hy', hw']

/-- The sign relation `(-1)^σ (-i)^r = (-1)^s i^r` when `σ + r ≡ s` modulo `2`. -/
theorem sign_I_pow {σ r s : ℕ} (h : (σ + r) % 2 = s % 2) :
    (-1 : ℂ) ^ σ * (-Complex.I) ^ r = (-1) ^ s * Complex.I ^ r := by
  rw [neg_pow Complex.I r, ← mul_assoc, ← pow_add, neg_one_pow_congr h]

/-- The parity condition of the final step for `C > A`. -/
theorem odd_CA {p q k : ℕ} (hpq : p < q) :
    Odd (k + (p + 1 + (q - p + k) % 2) % 2 + q % 2) := by
  rw [Nat.odd_iff]
  omega

/-- The coefficient of the first function along `r₁(t) r₂(π/2)` for `C > A`. -/
theorem coeff_kappa_CA {c : ℂ} {r m s : ℕ} (hs : s ≤ m)
    (hsgn : c * (-Complex.I) ^ r = (-1) ^ s * Complex.I ^ r) :
    coeff (-((m - s : ℕ) : ℤ)) (fun t => (Gp h42 vA vB r m + c • Gm h42 vA vB r m)
      ((blockRotation 4 1 t : Matrix (Fin 4) (Fin 4) ℝ) *
        ((blockRotation 4 2 (Real.pi / 2) : Langlands.GeneralLinear 4 ℝ) :
          Matrix (Fin 4) (Fin 4) ℝ))) ≠ 0 := by
  refine coeff_ne_zero_of_eq (fun t => ?_)
    (coeff_pair_neg_ne_zero (pow_ne_zero r Complex.I_ne_zero) m s hs)
  obtain ⟨h1, h2, h3, h4⟩ := values_CA_kappa t
  have e : ((blockRotation 4 2 (Real.pi / 2) : Langlands.GeneralLinear 4 ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) =
      (blockRotation 4 2 (Real.pi / 2) : Matrix (Fin 4) (Fin 4) ℝ) * 1 := (mul_one _).symm
  rw [e]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Gp_apply, Gm_apply, h1, h2, h3, h4]
  linear_combination (Complex.I * expMode (-1) t + -Complex.I) ^ m * hsgn

/-- The final coefficient along `r₀(θ)` for `C > A`. -/
theorem coeff_rot0_CA {g c : ℂ} (hg : g ≠ 0) {r m s : ℕ} (hs : s ≤ 1) (hm : 0 < m)
    (hsgn : c * (-Complex.I) ^ r = (-1) ^ s * Complex.I ^ r) :
    coeff (((1 + s) % 2 : ℕ) : ℤ) (fun θ => 2 * (Real.pi : ℂ) * g *
      ((yZ h41 vA ^ r * wp vA vB ^ m) (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ) -
        c * (yZ h41 vA ^ r * wp vA vB ^ m)
          (fl 3 * (fl 2 * (blockRotation 4 0 θ : Matrix (Fin 4) (Fin 4) ℝ))))) ≠ 0 := by
  refine coeff_ne_zero_of_eq (fun θ => ?_)
    (coeff_pair_pos_ne_zero (mul_ne_zero hg (pow_ne_zero r Complex.I_ne_zero)) m s hs hm)
  obtain ⟨h1, h2⟩ := values_CA_rot0 r m θ
  rw [h1, h2]
  linear_combination (-(2 * (Real.pi : ℂ) * g) * (-Complex.I * expMode 1 θ + 1) ^ m) * hsgn

set_option maxHeartbeats 1000000 in
/-- **The engine for `C > A`.** Let `p = |m(d)| < q = |m(e)|`, `A = k`, `B = p - k`,
`C = q - p + k`, `r + m = q + 1`, `σ = C mod 2`. Given the flat functional `ψ₀` at the block `0`
(exponents `a₀`, signs `e₀`, values `μ₀(±m)`) and a tail multiplier `μ₁` at the middle block, the
chain `ψ₀`, tail at `1`, generic at `2`, followed by the dichotomy at `1` and the final binomial
functional at `0`, gives the conclusion. -/
theorem engine_CA {d e : ComplexCharacterData} {p q k r m : ℕ}
    (hpd : d.weight.natAbs = p) (hqe : e.weight.natAbs = q) (hk : 0 < k) (hkp : k ≤ p)
    (hpq : p < q) (hrm : r + m = q + 1) (hmp : p < m) (hmpar : (m + p) % 2 = 1)
    {μ0 : ℤ → ℂ} {a0 : Fin 4 → ℂ} {e0 : Fin 4 → Fin 2}
    (hψ0 : IsRealJacquetFunctional 4 (realStandardRep 4 [RealBlock.induced d, RealBlock.induced e])
      (realStandardLie 4 [RealBlock.induced d, RealBlock.induced e])
      (blockJacquet 4 [RealBlock.induced d, RealBlock.induced e] 0 μ0) a0 e0)
    (hC : expo a0 1 - expo a0 3 = ((q - p + k : ℕ) : ℂ))
    (hB : expo a0 1 - expo a0 2 = -((p - k : ℕ) : ℂ))
    (hQ : expo a0 2 - expo a0 3 = (q : ℂ))
    (hA : expo a0 0 - expo a0 2 = (k : ℂ))
    (he0 : (e0 0).val = (p + 1 + (q - p + k) % 2) % 2) (he1 : (e0 1).val = (q - p + k) % 2)
    (he2 : (e0 2).val = (q + 1) % 2) (he3 : (e0 3).val = 0)
    (hμ0p : μ0 (m : ℤ) = 1) (hμ0m : μ0 (-(m : ℤ)) = (-1) ^ ((q - p + k) % 2))
    {μ1 : ℤ → ℂ} (hrec1 : IsRecurrent (1 - ((p - k : ℕ) : ℂ)) (((p + 1 + k) % 2 : ℕ) : ℤ) μ1)
    (hsym1 : IsSymmetric (((p + 1 + k) % 2 : ℕ) : ℤ) ((-1) ^ ((p + 1 + k) % 2)) μ1)
    (hμ1 : μ1 (-((m - k % 2 : ℕ) : ℤ)) ≠ 0) :
    RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e] := by
  have hsgn : (-1 : ℂ) ^ ((q - p + k) % 2) * (-Complex.I) ^ r =
      (-1) ^ (k % 2) * Complex.I ^ r := sign_I_pow (by omega)
  -- the arithmetic facts of the main evaluation (stated early: `omega` is slow in the later context)
  have ar_rm : 0 < r + m := by omega
  have ar_km : k % 2 ≤ m := by omega
  have ar_j : ∀ j : ℤ, |j| + 1 < ((r + m : ℕ) : ℤ) → |j| < (q : ℤ) := fun j hj => by omega
  have ar_s : k % 2 ≤ 1 := by omega
  have ar_m : 0 < m := by omega
  have ar_par : Even (((r + m : ℕ) : ℤ) - (((q + 1) % 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff]
    omega
  -- the tail step at the middle block
  have hpar1 : par h41 e0 = (p + 1 + k) % 2 := by
    unfold par
    rw [ia41, ib41, he1, he2]
    omega
  have hδ1 : expo a0 (ia h41) - expo a0 (ib h41) + 1 = 1 - ((p - k : ℕ) : ℂ) := by
    rw [ia41, ib41, hB]
    ring
  have hJ1 := isJacquet_cross h41 (expo a0) e0 (μ := μ1) (by rw [hδ1, hpar1]; exact hrec1)
    (by rw [hpar1]; exact hsym1)
  -- the generic step at the block `2`
  have hx1 : ∀ i, expo (crossExp h41 (expo a0)) i = expo a0 (sw h41 i) := fun i => by
    rw [expo_crossExp]
    rfl
  have hpar2 : par h42 (e0 ∘ sw h41) = (q - p + k) % 2 := by
    unfold par
    simp only [Function.comp_apply]
    rw [ia42, ib42, sw41_2, sw41_3, he1, he3]
    omega
  set ε2 : ℤ := ((par h42 (e0 ∘ sw h41) : ℕ) : ℤ) with hε2def
  have hε2 : ε2 = 0 ∨ ε2 = 1 := par_cases h42 _
  have hν : 0 < (((q - p + k : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 0 < q - p + k)
  have hδ2 : expo (crossExp h41 (expo a0)) (ia h42) - expo (crossExp h41 (expo a0)) (ib h42) + 1 =
      ((q - p + k : ℕ) : ℂ) + 1 := by
    rw [hx1, hx1, ia42, ib42, sw41_2, sw41_3, hC]
  have hsym2 : IsSymmetric (par h42 (e0 ∘ sw h41)) ((-1) ^ par h42 (e0 ∘ sw h41))
      (genericMultiplier ((q - p + k : ℕ) : ℂ) ε2) :=
    isSymmetric_genericMultiplier ((q - p + k : ℕ) : ℂ) hε2
  have hJ2 := isJacquet_cross h42 (expo (crossExp h41 (expo a0))) (e0 ∘ sw h41)
    (by rw [hδ2]; exact isRecurrent_genericMultiplier hν hε2) hsym2
  have hμ2 : ∀ j, genericMultiplier ((q - p + k : ℕ) : ℂ) ε2 j ≠ 0 := by
    refine genericMultiplier_ne_zero hν hε2 fun m' h => ?_
    have h' : ((q - p + k : ℕ) : ℤ) = ε2 + 2 * m' + 1 := by exact_mod_cast h
    rw [hε2def, hpar2] at h'
    omega
  -- the exponents and signs after the two steps
  have hT : ∀ i, expo (crossExp h42 (expo (crossExp h41 (expo a0)))) i =
      expo a0 (sw h41 (sw h42 i)) := fun i => by
    rw [expo_crossExp, expo_crossExp]
    rfl
  have hE0 : ((e0 ∘ sw h41) ∘ sw h42) 0 = e0 0 := by
    simp only [Function.comp_apply, sw42_0, sw41_0]
  have hE1 : ((e0 ∘ sw h41) ∘ sw h42) 1 = e0 2 := by
    simp only [Function.comp_apply, sw42_1, sw41_1]
  have hE2 : ((e0 ∘ sw h41) ∘ sw h42) 2 = e0 3 := by
    simp only [Function.comp_apply, sw42_2, sw41_3]
  have hE3 : ((e0 ∘ sw h41) ∘ sw h42) 3 = e0 1 := by
    simp only [Function.comp_apply, sw42_3, sw41_2]
  -- the flipped signs of the final functional
  obtain ⟨e', he'0, he'1, he'2, he'3⟩ : ∃ e' : Fin 4 → Fin 2, e' 0 = e0 0 ∧
      (e' 1).val = q % 2 ∧ (e' 2).val = 1 ∧ e' 3 = e0 1 :=
    ⟨![e0 0, ⟨q % 2, Nat.mod_lt _ two_pos⟩, 1, e0 1], rfl, rfl, rfl, rfl⟩
  have hpar3 : par h40 e' = (1 + k % 2) % 2 := by
    unfold par
    rw [ia40, ib40, he'0, he0, he'1]
    omega
  refine exists_of_dichotomy ((frobMap hJ2).comp ((frobMap hJ1).comp (frobMap hψ0)))
    (fun κ v => ?_) (fun Y v => ?_) h41 (k₁ := q) (by omega) ?_ ?_ (e' := e') ?_ ?_ ?_ h40
    (k₂ := k) hk ?_ ?_ ?_
  · simp only [LinearMap.comp_apply, frobMap_rep]
  · simp only [LinearMap.comp_apply, frobMap_lie]
  · rw [hT, hT, ia41, ib41, sw42_1, sw41_1, sw42_2, sw41_3, hQ]
  · rw [ia41, ib41, hE1, hE2, he2, he3, Nat.odd_iff]
    omega
  · intro i h1 h2
    fin_cases i
    · show e' 0 = ((e0 ∘ sw h41) ∘ sw h42) 0
      rw [he'0, hE0]
    · exact absurd rfl h1
    · exact absurd rfl h2
    · show e' 3 = ((e0 ∘ sw h41) ∘ sw h42) 3
      rw [he'3, hE3]
  · rw [ia41, he'1, hE1, he2]
    exact neg_one_pow_mod_flip q
  · rw [ib41, he'2, hE2, he3]
    norm_num
  · rw [hT, hT, ia40, ib40, sw42_0, sw41_0, sw42_1, sw41_1, hA]
  · rw [ia40, ib40, he'0, he0, he'1]
    exact odd_CA hpq
  -- the main evaluation
  intro hwin
  have hQ0 : (-1 : ℂ) ^ (![m, 0, r + m, 0] : Fin 4 → ℕ) 0 = (-1) ^ (d.weight.natAbs + 1) := by
    show (-1 : ℂ) ^ m = _
    rw [hpd]
    exact neg_one_pow_congr (by omega)
  have hQ2 : (-1 : ℂ) ^ (![m, 0, r + m, 0] : Fin 4 → ℕ) 2 = (-1) ^ (e.weight.natAbs + 1) := by
    show (-1 : ℂ) ^ (r + m) = _
    rw [hrm, hqe]
  obtain ⟨v, hv⟩ := exists_test_of (d := d) (e := e) (Fp_mem_PF h42 vA vB r m)
    (isSignEq_Fp2 vA vB r m) hQ0 (by simp) hQ2 (by simp) (Fp2_rot0 vA vB r m)
    (by rw [hpd, abs_of_nonneg (Int.natCast_nonneg _)]; omega) (Fp2_rot2 vA vB r m)
    (by rw [hqe, abs_of_nonneg (Int.natCast_nonneg _)]; omega)
  refine ⟨v, ?_⟩
  -- the first step on `SO(4)`
  have hH1 : Gp h42 vA vB r m + (-1 : ℂ) ^ ((q - p + k) % 2) • Gm h42 vA vB r m ∈
      Sm vA vB r m :=
    Submodule.add_mem _ (Gp_mem_Sm h42 vA vB r m)
      (Submodule.smul_mem _ _ (Gm_mem_Sm h42 vA vB r m))
  have hw0 : ∀ κ ∈ SOset 4, ((frobMap hψ0 v : KF 4 _) : Langlands.GeneralLinear 4 ℝ → ℂ) κ =
      (Gp h42 vA vB r m + (-1 : ℂ) ^ ((q - p + k) % 2) • Gm h42 vA vB r m)
        (κ : Matrix (Fin 4) (Fin 4) ℝ) := by
    intro κ hκ
    rw [frobMap_eq_two_mode hψ0 v (N := (m : ℤ)) (by omega)
      (test_two_mode hv (Fp2_rot0 vA vB r m)) hκ, hμ0p, hμ0m]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hpar' : Even (((r + m : ℕ) : ℤ) - ((par h41 ((e0 ∘ sw h41) ∘ sw h42) : ℕ) : ℤ)) := by
    have : par h41 ((e0 ∘ sw h41) ∘ sw h42) = (q + 1) % 2 := by
      unfold par
      rw [ia41, ib41, hE1, hE2, he2, he3, Nat.add_zero, Nat.mod_mod]
    rw [this]
    exact ar_par
  rw [hpar3]
  refine main_value ar_rm h42 (hasExpTop_Sm2 vA vB r m) hJ1 hJ2 hμ2 hH1 (frobMap hψ0 v) hw0
    (blockRotation_mem_SOset (n := 4) 2 (Real.pi / 2)) hμ1
    (coeff_kappa_CA ar_km hsgn)
    (fun j hj κ hκ => hwin v j (ar_j j hj) κ hκ) hpar' (fun g hg => ?_)
  simp only [hE2, hE3, he1, he3, zero_add]
  exact coeff_rot0_CA hg ar_s ar_m hsgn

/-- **The flat functional at the block `0`.** For `c` even the trivial multiplier, for `c` odd the
sign multiplier (flat since the block-`0` coefficients of weight `< |m(d)|` vanish), with the
natural signs at the blocks `2, 3` and the signs at the block `0` flipped for `c` odd. -/
theorem exists_flat_CA (d e : ComplexCharacterData) (c : ℕ) {m : ℕ} (hm : 0 < m) :
    ∃ (μ0 : ℤ → ℂ) (e0 : Fin 4 → Fin 2),
      IsRealJacquetFunctional 4 (realStandardRep 4 [RealBlock.induced d, RealBlock.induced e])
        (realStandardLie 4 [RealBlock.induced d, RealBlock.induced e])
        (blockJacquet 4 [RealBlock.induced d, RealBlock.induced e] 0 μ0)
        (fun i : Fin 4 => realPositionExponent [RealBlock.induced d, RealBlock.induced e] (i : ℕ) +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) e0 ∧
      (e0 0).val = (d.weight.natAbs + 1 + c % 2) % 2 ∧ (e0 1).val = c % 2 ∧
      (e0 2).val = (e.weight.natAbs + 1) % 2 ∧ (e0 3).val = 0 ∧
      μ0 (m : ℤ) = 1 ∧ μ0 (-(m : ℤ)) = (-1) ^ (c % 2) := by
  have hb0 : 0 + 1 < 4 := by norm_num
  have hτ := fun (i : Fin 4) (x : ℝ) =>
    realPositionCharacter_exp [RealBlock.induced d, RealBlock.induced e] i x
  have hc0 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) := realInducedFirstCharacter_neg_one d
  have hc1 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) = 1 :=
    realInducedSecondCharacter_neg_one d
  have hc2 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 2 (-1) =
      (-1 : ℂ) ^ (e.weight.natAbs + 1) := realInducedFirstCharacter_neg_one e
  have hc3 : realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 3 (-1) = 1 :=
    realInducedSecondCharacter_neg_one e
  have hpar : (-1 : ℂ) ^ ((d.weight.natAbs : ℤ) + 1) =
      realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] (0 + 1) (-1) := by
    show (-1 : ℂ) ^ ((d.weight.natAbs : ℤ) + 1) =
      realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1)
    rw [hc0, hc1, mul_one, ← zpow_natCast]
    push_cast
    rfl
  set e0 : Fin 4 → Fin 2 := ![⟨(d.weight.natAbs + 1 + c % 2) % 2, Nat.mod_lt _ two_pos⟩,
    ⟨c % 2, Nat.mod_lt _ two_pos⟩, ⟨(e.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩, 0]
    with he0def
  have hoff : ∀ i : Fin 4, i ≠ ia hb0 → i ≠ ib hb0 →
      (-1 : ℂ) ^ (e0 i).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] i (-1) := by
    intro i h1 h2
    fin_cases i
    · exact absurd rfl h1
    · exact absurd rfl h2
    · show (-1 : ℂ) ^ ((e.weight.natAbs + 1) % 2) = _
      rw [hc2, ← neg_one_pow_eq_pow_mod_two]
    · show (-1 : ℂ) ^ 0 = _
      rw [hc3]
      ring
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc
  · have hp' : (-1 : ℂ) ^ (e0 (ia hb0)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) * 1 := by
      show (-1 : ℂ) ^ ((d.weight.natAbs + 1 + c % 2) % 2) = _
      rw [hc, hc0, add_zero, mul_one, ← neg_one_pow_eq_pow_mod_two]
    have hq' : (-1 : ℂ) ^ (e0 (ib hb0)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] (0 + 1) (-1) * 1 := by
      show (-1 : ℂ) ^ (c % 2) =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) * 1
      rw [hc, hc1]
      ring
    have hm' : (1 : ℂ) = (-1) ^ (c % 2) := by
      rw [hc]
      ring
    exact ⟨fun _ => 1, e0, isRealJacquetFunctional_blockJacquet_flat hb0 hτ hpar
      (fun _ _ _ => ⟨rfl, rfl⟩) (isSymmetric_one _) hoff hp' hq', rfl, rfl, rfl, rfl, rfl, hm'⟩
  · have hδ : (realPositionExponent [RealBlock.induced d, RealBlock.induced e] 0 +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) -
        (realPositionExponent [RealBlock.induced d, RealBlock.induced e] 1 +
          (((4 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) = (d.weight.natAbs : ℂ) + 1 := by
      show (d.exponent + (d.weight.natAbs : ℂ) / 2 + (((4 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) -
        (d.exponent - (d.weight.natAbs : ℂ) / 2 + (((4 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ)) =
          (d.weight.natAbs : ℂ) + 1
      push_cast
      ring
    have hp' : (-1 : ℂ) ^ (e0 (ia hb0)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 0 (-1) * -1 := by
      show (-1 : ℂ) ^ ((d.weight.natAbs + 1 + c % 2) % 2) = _
      rw [hc, hc0, ← neg_one_pow_eq_pow_mod_two]
      ring
    have hq' : (-1 : ℂ) ^ (e0 (ib hb0)).val =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] (0 + 1) (-1) * -1 := by
      show (-1 : ℂ) ^ (c % 2) =
        realPositionCharacter [RealBlock.induced d, RealBlock.induced e] 1 (-1) * -1
      rw [hc, hc1]
      ring
    have hm1 : ((Int.sign (m : ℤ) : ℤ) : ℂ) = 1 := by
      rw [Int.sign_eq_one_of_pos (by omega)]
      simp
    have hm2 : ((Int.sign (-(m : ℤ)) : ℤ) : ℂ) = (-1) ^ (c % 2) := by
      rw [hc, Int.sign_eq_neg_one_of_neg (by omega)]
      simp
    exact ⟨fun j : ℤ => ((Int.sign j : ℤ) : ℂ), e0,
      isRealJacquetFunctional_blockJacquet_flat hb0 hτ hpar
        (flat_sign hb0 hpar (w := d.weight.natAbs) ⟨0, by ring⟩
          (fun f j hj => (Submodule.mem_inf.mp f.2).1.2 0 d rfl j
            (by rwa [Int.abs_eq_natAbs d.weight]) 1) hδ)
        (isSymmetric_sign _) hoff hp' hq', rfl, rfl, rfl, rfl, hm1, hm2⟩

/-- **Two interlaced linked induction blocks with `|m(d)| < |m(e)|`.** -/
theorem interlaced_CA {d e : ComplexCharacterData} {k : ℕ} (hk : 0 < k)
    (hkp : k ≤ d.weight.natAbs) (hpq : d.weight.natAbs < e.weight.natAbs)
    (hlink : d.exponent - e.exponent =
      ((((d.weight.natAbs : ℤ) - e.weight.natAbs).natAbs : ℕ) : ℂ) / 2 + k) :
    RealLinkedJacquetFunctionalExists 4 [RealBlock.induced d, RealBlock.induced e] := by
  have hlink' : d.exponent - e.exponent =
      ((e.weight.natAbs : ℂ) - d.weight.natAbs) / 2 + k := by
    rw [hlink, natAbs_sub_cast, min_eq_left hpq.le]
    ring
  obtain ⟨μ0, e0, hψ0, he0, he1, he2, he3, hμ0p, hμ0m⟩ :=
    exists_flat_CA d e (e.weight.natAbs - d.weight.natAbs + k)
      (m := e.weight.natAbs + 1 - (e.weight.natAbs - d.weight.natAbs) % 2) (by omega)
  have hx : ∀ i : Fin 4, expo (fun i : Fin 4 =>
      realPositionExponent [RealBlock.induced d, RealBlock.induced e] (i : ℕ) +
        (((4 : ℕ) : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) i =
      realPositionExponent [RealBlock.induced d, RealBlock.induced e] (i : ℕ) := fun i => by
    simp only [expo]
    ring
  obtain ⟨μ1, hrec1, hsym1, hμ1⟩ := exists_tail_mult (B := d.weight.natAbs - k)
    (ε := (d.weight.natAbs + 1 + k) % 2) (by omega)
    (j := -((e.weight.natAbs + 1 - (e.weight.natAbs - d.weight.natAbs) % 2 - k % 2 : ℕ) : ℤ))
    (by rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]; omega)
    (by rw [Int.even_iff]; omega)
  refine engine_CA rfl rfl hk hkp hpq (r := (e.weight.natAbs - d.weight.natAbs) % 2)
    (m := e.weight.natAbs + 1 - (e.weight.natAbs - d.weight.natAbs) % 2) (by omega)
    (by omega) (by omega) hψ0 ?_ ?_ ?_ ?_ he0 he1 he2 he3 hμ0p hμ0m hrec1 hsym1 hμ1
  · rw [hx, hx]
    show (d.exponent - (d.weight.natAbs : ℂ) / 2) - (e.exponent - (e.weight.natAbs : ℂ) / 2) = _
    rw [Nat.cast_add, Nat.cast_sub hpq.le]
    linear_combination hlink'
  · rw [hx, hx]
    show (d.exponent - (d.weight.natAbs : ℂ) / 2) - (e.exponent + (e.weight.natAbs : ℂ) / 2) = _
    rw [Nat.cast_sub hkp]
    linear_combination hlink'
  · rw [hx, hx]
    show (e.exponent + (e.weight.natAbs : ℂ) / 2) - (e.exponent - (e.weight.natAbs : ℂ) / 2) = _
    ring
  · rw [hx, hx]
    show (d.exponent + (d.weight.natAbs : ℂ) / 2) - (e.exponent + (e.weight.natAbs : ℂ) / 2) = _
    linear_combination hlink'

end CA

end RealInterlacedJacquet

/-! ## The interlaced case -/

/-- **Two interlaced linked induction blocks.** The case `|m(e)| ≤ |m(d)|` (`A ≥ C`) is
`interlaced_AC`, the case `|m(d)| < |m(e)|` (`C > A`) is `interlaced_CA`. -/
theorem realInterlacedInducedInducedLinkedJacquetFunctional :
    RealInterlacedInducedInducedLinkedJacquetFunctionalStatement := by
  intro d e k _ _ hk hkmin hlink
  rcases le_or_gt e.weight.natAbs d.weight.natAbs with h | h
  · exact RealInterlacedJacquet.interlaced_AC hk (le_trans hkmin (min_le_right _ _)) h hlink
  · exact RealInterlacedJacquet.interlaced_CA hk (le_trans hkmin (min_le_left _ _)) h hlink

/-- **Two linked induction blocks (II).** The separated case is
`RealBlockFlatJacquet.separatedInducedInducedLinkedJacquetFunctional`, the interlaced case is
`realInterlacedInducedInducedLinkedJacquetFunctional`. -/
theorem realInducedInducedLinkedJacquetFunctional :
    RealInducedInducedLinkedJacquetFunctionalStatement :=
  RealBlockFlatJacquet.realInducedInducedLinkedJacquetFunctional_of_interlaced
    realInterlacedInducedInducedLinkedJacquetFunctional

end Langlands.Archimedean
