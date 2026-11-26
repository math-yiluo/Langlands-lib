import Langlands.Global.AdelicLeadingCuspidalComponents
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LiminfLimsup

/-! # Uniform bounds for a constant-term exponent component on a split ray -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Polynomial Filter
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

private theorem exists_polynomial_on_nat_line {V : Type*} [AddCommGroup V] [Module ℝ V]
    {d : ℕ} {Q : V → ℂ} (hQ : Q ∈ polynomialFunctions V d) (x : V) :
    ∃ p : ℂ[X], p.natDegree ≤ d ∧ ∀ n : ℕ, p.eval (n : ℂ) = Q ((n : ℝ) • x) := by
  classical
  induction hQ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, hk, ℓ, rfl⟩ := hf
    refine ⟨C (∏ j, ((ℓ j x : ℝ) : ℂ)) * X ^ k,
      (natDegree_C_mul_le _ _).trans (by simpa only [natDegree_X_pow] using hk), ?_⟩
    intro n
    simp only [eval_mul, eval_C, eval_pow, eval_X, map_smul, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  | zero => exact ⟨0, by simp, fun _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp, hfp⟩ := hf
    obtain ⟨q, hq, hgq⟩ := hg
    exact ⟨p + q, (natDegree_add_le _ _).trans (max_le hp hq),
      fun n => by simp only [eval_add, Pi.add_apply, hfp, hgq]⟩
  | smul z f _ hf =>
    obtain ⟨p, hp, hfp⟩ := hf
    exact ⟨C z * p, (natDegree_C_mul_le _ _).trans hp,
      fun n => by simp only [eval_mul, eval_C, Pi.smul_apply, smul_eq_mul, hfp]⟩

private theorem norm_polynomial_eval_nat_le (p : ℂ[X]) {d : ℕ} (hp : p.natDegree ≤ d) (n : ℕ) :
    ‖p.eval (n : ℂ)‖ ≤ (∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖) * (max 1 (n : ℝ)) ^ d := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hd : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 (n : ℕ) : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [norm_mul, norm_pow, h1]
  exact mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ (Nat.cast_nonneg n) (le_max_right 1 (n : ℝ)) i).trans
      (pow_le_pow_right₀ (le_max_left _ _) hd)) (norm_nonneg _)

/-- A polynomial of bounded degree has a common growth bound in terms of the largest absolute
value at the consecutive integer sample points. -/
private theorem exists_uniform_norm_polynomial_eval_nat_le (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℂ[X]) (M : ℝ), p.natDegree ≤ d →
      (∀ k ≤ d, ‖p.eval (k : ℂ)‖ ≤ M) →
        ∀ n : ℕ, ‖p.eval (n : ℂ)‖ ≤ C * M * (max 1 (n : ℝ)) ^ d := by
  let s := Finset.range (d + 1)
  let v (i : ℕ) := (i : ℂ)
  have hv : Set.InjOn v s := Nat.cast_injective.injOn
  let B (i : ℕ) := Lagrange.basis s v i
  let b (i : ℕ) := ∑ j ∈ s, ‖(B i).coeff j‖
  refine ⟨∑ i ∈ s, b i, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  intro p M hp hM n
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le d))
  have hd : p.degree < (s.card : WithBot ℕ) := by
    refine (degree_le_natDegree (p := p)).trans_lt ?_
    rw [show s.card = d + 1 by simp [s]]
    exact_mod_cast Nat.lt_succ_of_le hp
  have heq : p.eval (n : ℂ) = ∑ i ∈ s, p.eval (i : ℂ) * (B i).eval (n : ℂ) := by
    conv_lhs => rw [Lagrange.eq_interpolate hv hd]
    simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, v, B]
  rw [heq, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hBi : (B i).natDegree ≤ d := by
    rw [Lagrange.natDegree_basis hv hi]
    simp [s]
  rw [norm_mul]
  calc
    _ ≤ M * (b i * (max 1 (n : ℝ)) ^ d) :=
      mul_le_mul (hM i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        (norm_polynomial_eval_nat_le (B i) hBi n) (norm_nonneg _) hM0
    _ = _ := by ring

namespace StandardParabolicFamily

open GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "P" => fam.P J
local notation "A" => AdelicGroupPoints F G

/-- Uniform bounds at fixed integer ray positions give the polynomial times character bound
for the whole component, with one degree and coefficient for all starting points. -/
theorem exists_rayBound_of_exponent_samples
    {lam : ComplexCharacterParameter F P} {f : A → ℂ} (hf : fam.HasUnnormalizedExponent J lam f)
    (a : fam.positiveSplitComponent J) {S : Set A} {B : A → ℝ} (hB : ∀ g ∈ S, 0 ≤ B g)
    (hSample : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ S,
      ‖f ((map F P G (fam.p J) a.val) ^ n * g)‖ ≤ C * B g) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (n : ℕ) (g : A), g ∈ S →
      ‖f ((map F P G (fam.p J) a.val) ^ n * g)‖ ≤
        C * B g * (max 1 (n : ℝ)) ^ d * ‖parameterPower F P lam a.val‖ ^ n := by
  obtain ⟨d, hOrb⟩ := hf
  let t := map F P G (fam.p J) a.val
  let r := ‖parameterPower F P lam a.val‖
  have hr : 0 < r := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  choose C hC hSample using hSample
  let s := Finset.range (d + 1)
  let M := ∑ i ∈ s, C i / r ^ i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => div_nonneg (hC i) (pow_nonneg hr.le i)
  obtain ⟨L, hL, hPoly⟩ := exists_uniform_norm_polynomial_eval_nat_le d
  refine ⟨d, L * M, mul_nonneg hL hM, fun n g hg => ?_⟩
  obtain ⟨Q, hQ, hEq⟩ := hOrb g
  obtain ⟨p, hp, he⟩ := exists_polynomial_on_nat_line hQ (characterLog F P a.val)
  have hLog (k : ℕ) : characterLog F P (a.val ^ k) = (k : ℝ) • characterLog F P a.val := by
    induction k with
    | zero => simp [characterLog_one]
    | succ k ih => rw [pow_succ, characterLog_mul, ih, Nat.cast_succ, add_smul, one_smul]
  have hPow (k : ℕ) : parameterPower F P (-lam) (a.val ^ k) =
      ((parameterPower F P lam a.val)⁻¹) ^ k := by
    rw [← parameterCharacter_apply, map_pow, Units.val_pow_eq_pow_val, parameterCharacter_apply]
    simp only [parameterPower, map_neg, LinearMap.neg_apply, Complex.exp_neg]
  have hNorm (k : ℕ) : ‖p.eval (k : ℂ)‖ * r ^ k = ‖f (t ^ k * g)‖ := by
    rw [he, ← hLog, ← hEq _ ((fam.positiveSplitComponent J).pow_mem a.property k)]
    simp only [unnormalizedAction, map_pow, hPow, norm_mul, norm_pow, norm_inv]
    change ‖f (t ^ k * g)‖ * r⁻¹ ^ k * r ^ k = _
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, mul_one]
  have hValues (k : ℕ) (hk : k ≤ d) : ‖p.eval (k : ℂ)‖ ≤ M * B g := by
    have hkr : k ∈ s := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    have hTerm : C k / r ^ k ≤ M :=
      Finset.single_le_sum (f := fun i => C i / r ^ i)
        (fun i _ => div_nonneg (hC i) (pow_nonneg hr.le i)) hkr
    calc
      _ ≤ (C k * B g) / r ^ k := (le_div_iff₀ (pow_pos hr _)).mpr
        ((hNorm k).trans_le (hSample k g hg))
      _ = (C k / r ^ k) * B g := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hTerm (hB g hg)
  rw [← hNorm n]
  exact mul_le_mul_of_nonneg_right ((hPoly p (M * B g) hp hValues n).trans_eq (by ring)) (pow_nonneg hr.le _)

/-- Any strictly larger exponential rate absorbs the polynomial factor in the uniform bound
from the samples. -/
theorem exists_rayBound_with_larger_rate
    {lam : ComplexCharacterParameter F P} {f : A → ℂ} (hf : fam.HasUnnormalizedExponent J lam f)
    (a : fam.positiveSplitComponent J) {S : Set A} {B : A → ℝ} (hB : ∀ g ∈ S, 0 ≤ B g)
    (hSample : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ S,
      ‖f ((map F P G (fam.p J) a.val) ^ n * g)‖ ≤ C * B g)
    (r : ℝ) (hr : ‖parameterPower F P lam a.val‖ < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (g : A), g ∈ S →
      ‖f ((map F P G (fam.p J) a.val) ^ n * g)‖ ≤ C * B g * r ^ n := by
  obtain ⟨d, C, hC, hRay⟩ := fam.exists_rayBound_of_exponent_samples J hf a hB hSample
  let z := ‖parameterPower F P lam a.val‖ / r
  have hr0 : 0 < r := (norm_nonneg _).trans_lt hr
  have hz : 0 ≤ z := div_nonneg (norm_nonneg _) hr0.le
  have hz1 : z < 1 := (div_lt_one hr0).mpr hr
  obtain ⟨L, hL⟩ := (tendsto_pow_const_mul_const_pow_of_lt_one d hz hz1).bddAbove_range
  let D := max 1 L
  have hD : 0 ≤ D := zero_le_one.trans (le_max_left _ _)
  have hAbsorb (n : ℕ) : (max 1 (n : ℝ)) ^ d * z ^ n ≤ D := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa only [Nat.cast_zero, max_eq_left zero_le_one, one_pow, pow_zero, mul_one] using le_max_left 1 L
    · have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
      rw [max_eq_right h1]
      exact (hL ⟨n, rfl⟩).trans (le_max_right _ _)
  refine ⟨C * D, mul_nonneg hC hD, fun n g hg => (hRay n g hg).trans ?_⟩
  have he : z * r = ‖parameterPower F P lam a.val‖ := div_mul_cancel₀ _ hr0.ne'
  rw [← he, mul_pow]
  calc
    _ = (C * B g) * ((max 1 (n : ℝ)) ^ d * z ^ n) * r ^ n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hAbsorb n) (mul_nonneg hC (hB g hg))) (pow_nonneg hr0.le _)
      |>.trans_eq (by ring)

end StandardParabolicFamily

open GroupScheme AdelicGroupPoints

/-- Fixed-position bounds along an integer split ray imply a uniform exponential bound at
any rate strictly above the norm of the component's character at the ray generator. -/
def AdelicExponentRayInterpolationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
      (lam : ComplexCharacterParameter F (fam.P J)) (f : AdelicGroupPoints F G → ℂ)
      (a : fam.positiveSplitComponent J) (S : Set (AdelicGroupPoints F G))
      (B : AdelicGroupPoints F G → ℝ) (r : ℝ),
      fam.HasUnnormalizedExponent J lam f →
      (∀ g ∈ S, 0 ≤ B g) →
      (∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ S,
        ‖f ((map F (fam.P J) G (fam.p J) a.val) ^ n * g)‖ ≤ C * B g) →
      ‖parameterPower F (fam.P J) lam a.val‖ < r →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (g : AdelicGroupPoints F G), g ∈ S →
        ‖f ((map F (fam.P J) G (fam.p J) a.val) ^ n * g)‖ ≤ C * B g * r ^ n

theorem adelicExponentRayInterpolation : AdelicExponentRayInterpolationStatement := by
  intro F _ _ G _ _ _ fam J lam f a S B r hf hB hSample hr
  exact fam.exists_rayBound_with_larger_rate J hf a hB hSample r hr

end Langlands.Global
