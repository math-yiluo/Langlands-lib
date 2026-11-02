import Langlands.Global.Arithmetic.SplitQuadraticPrerequisites
import Langlands.Global.Arithmetic.QuadraticRootSupport
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic

namespace Langlands.Global

open Polynomial IntermediateField

universe u

private lemma signedPrime_not_isSquare (s : ℚ) (hs : s ^ 2 = 1)
    {q : ℕ} (hq : q.Prime) : ¬ IsSquare (s * q) := by
  let : Fact q.Prime := ⟨hq⟩
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hv : padicValRat q s = 0 := by
    have h := congrArg (padicValRat q) hs
    simp only [padicValRat.pow, Nat.cast_ofNat, padicValRat.one] at h
    omega
  intro h
  have he := (Rat.isSquare_iff_even_factorization.mp h).2 q hq
  rw [padicValRat.mul hs0 (Nat.cast_ne_zero.mpr hq.ne_zero), hv,
    padicValRat.self hq.one_lt, zero_add] at he
  norm_num at he

private lemma distinctPrime_product_not_isSquare {q r : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) : ¬ IsSquare ((q : ℚ) * r) := by
  let : Fact q.Prime := ⟨hq⟩
  have hnd : ¬ q ∣ r := by simpa [Nat.prime_dvd_prime_iff_eq hq hr] using hqr
  intro h
  have he := (Rat.isSquare_iff_even_factorization.mp h).2 q hq
  rw [padicValRat.mul (Nat.cast_ne_zero.mpr hq.ne_zero)
      (Nat.cast_ne_zero.mpr hr.ne_zero), padicValRat.self hq.one_lt,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd] at he
  norm_num at he

private lemma sqrt_not_rational {K : Type u} [Field K] [CharZero K]
    {d : ℚ} {x : K} (hd : ¬ IsSquare d) (hx : x ^ 2 = algebraMap ℚ K d)
    (r : ℚ) : x ≠ algebraMap ℚ K r := by
  intro h
  apply hd
  refine ⟨r, ?_⟩
  apply (algebraMap ℚ K).injective
  simpa [h, map_mul, pow_two] using hx.symm

private lemma sqrt_adjoin_expression {K : Type u} [Field K] [CharZero K]
    {d : ℚ} {x y : K} (hd : ¬ IsSquare d) (hx : x ^ 2 = algebraMap ℚ K d)
    (hy : y ∈ ℚ⟮x⟯) :
    ∃ a b : ℚ, y = algebraMap ℚ K a + algebraMap ℚ K b * x := by
  let pb := adjoin.powerBasis (squareRoot_isIntegral hx)
  obtain ⟨f, hf, he⟩ := pb.exists_eq_aeval ⟨y, hy⟩
  have hdim : pb.dim = 2 := by
    change (minpoly ℚ x).natDegree = 2
    rw [squareRoot_minpoly hd hx, natDegree_X_pow_sub_C]
  rw [hdim] at hf
  rw [f.eq_X_add_C_of_natDegree_le_one (by omega)] at he
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  have h := congrArg (fun z : ℚ⟮x⟯ => (z : K)) he
  simpa [pb, add_comm] using h

private lemma sqrt_same_adjoin_product_isSquare {K : Type u} [Field K] [CharZero K]
    {d e : ℚ} {x y : K} (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hx : x ^ 2 = algebraMap ℚ K d) (hy : y ^ 2 = algebraMap ℚ K e)
    (hmem : y ∈ ℚ⟮x⟯) : IsSquare (d * e) := by
  obtain ⟨a, b, hab⟩ := sqrt_adjoin_expression hd hx hmem
  have hrel : algebraMap ℚ K (2 * a * b) * x =
      algebraMap ℚ K (e - a ^ 2 - b ^ 2 * d) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination hy - (algebraMap ℚ K b) ^ 2 * hx - (y + algebraMap ℚ K a + algebraMap ℚ K b * x) * hab
  have hab0 : a * b = 0 := by
    by_contra hab0
    have hn : (2 * a * b : ℚ) ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) (by aesop)) (by aesop)
    apply sqrt_not_rational hd hx ((e - a ^ 2 - b ^ 2 * d) / (2 * a * b))
    rw [map_div₀]
    have hnK : algebraMap ℚ K (2 * a * b) ≠ 0 := by
      intro hh
      exact hn ((algebraMap ℚ K).injective (by simpa using hh))
    apply (eq_div_iff hnK).2
    simpa [mul_comm] using hrel
  have hb : b ≠ 0 := by
    intro hb
    exact sqrt_not_rational he hy a (by simpa [hb] using hab)
  have ha : a = 0 := (mul_eq_zero.mp hab0).resolve_right hb
  have hed : e = b ^ 2 * d := by
    apply (algebraMap ℚ K).injective
    push_cast
    rw [ha, map_zero, zero_add] at hab
    rw [hab, mul_pow, hx] at hy
    exact hy.symm
  refine ⟨b * d, ?_⟩
  rw [hed]
  ring

private lemma finite_signedPrimes_square_in_numberField (K : Type u) [Field K] [NumberField K]
    (s : ℚ) (hs : s ^ 2 = 1) :
    {q : ℕ | q.Prime ∧ IsSquare (algebraMap ℚ K (s * q))}.Finite := by
  classical
  let T := {q : ℕ // q.Prime ∧ IsSquare (algebraMap ℚ K (s * q))}
  let x : T → K := fun q => q.property.2.choose
  have hx (q : T) : x q ^ 2 = algebraMap ℚ K (s * q.val) := by
    simpa only [pow_two] using q.property.2.choose_spec.symm
  let f : T → IntermediateField ℚ K := fun q => ℚ⟮x q⟯
  have hfin : Finite (IntermediateField ℚ K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ K
      (Field.exists_primitive_element ℚ K)
  have hf : Function.Injective f := by
    intro q r h
    by_contra hne
    have hqr : q.val ≠ r.val := fun h => hne (Subtype.ext h)
    have hmem : x r ∈ ℚ⟮x q⟯ := by
      change f q = f r at h
      rw [← show f q = ℚ⟮x q⟯ from rfl, h]
      exact mem_adjoin_simple_self ℚ (x r)
    have hc := sqrt_same_adjoin_product_isSquare
      (signedPrime_not_isSquare s hs q.property.1)
      (signedPrime_not_isSquare s hs r.property.1) (hx q) (hx r) hmem
    have heq : (s * q.val) * (s * r.val) = (q.val : ℚ) * r.val := by
      calc
        _ = s ^ 2 * ((q.val : ℚ) * r.val) := by ring
        _ = _ := by rw [hs, one_mul]
    exact distinctPrime_product_not_isSquare q.property.1 r.property.1 hqr (heq ▸ hc)
  have : Finite T := Finite.of_injective f hf
  exact @Set.toFinite ℕ _ this

private lemma padic_isSquare_of_congruent_one (p : ℕ) [Fact p.Prime]
    (d : ℤ) (hd : (4 * p : ℤ) ∣ 1 - d) :
    IsSquare (algebraMap ℚ (Padic p) (d : ℚ)) := by
  obtain ⟨k, hk⟩ := hd
  have h2 : (2 : ℤ_[p]) ≠ 0 := by norm_num
  have h2pos : 0 < ‖(2 : ℤ_[p])‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr h2)
  have hp : ‖(p : ℤ_[p])‖ < 1 := by
    simpa only [PadicInt.norm_p, Padic.norm_p] using (Padic.norm_p_lt_one (p := p))
  have h4 : ‖(4 : ℤ_[p])‖ = ‖(2 : ℤ_[p])‖ ^ 2 := by
    rw [← norm_pow]
    norm_num
  have hnorm : ‖(1 : ℤ_[p]) - d‖ < ‖(2 : ℤ_[p])‖ ^ 2 := by
    calc
      _ = (‖(2 : ℤ_[p])‖ ^ 2 * ‖(p : ℤ_[p])‖) * ‖(k : ℤ_[p])‖ := by
        have hh := congrArg (fun z : ℤ => (z : ℤ_[p])) hk
        push_cast at hh
        rw [hh, norm_mul, norm_mul, h4]
      _ ≤ ‖(2 : ℤ_[p])‖ ^ 2 * ‖(p : ℤ_[p])‖ :=
        mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
      _ < ‖(2 : ℤ_[p])‖ ^ 2 := by nlinarith
  obtain ⟨z, hz, _⟩ := hensels_lemma
    (F := (X ^ 2 - C d : ℤ[X])) (a := (1 : ℤ_[p])) (by simpa [map_ofNat] using hnorm)
  have hz2 : z ^ 2 = (d : ℤ_[p]) := by simpa [sub_eq_zero] using hz
  refine ⟨(z : Padic p), ?_⟩
  have hh := congrArg (fun z : ℤ_[p] => (z : Padic p)) hz2
  simpa [pow_two] using hh.symm

/-- A rational of either strict sign can be a local square at any prescribed
prime while remaining a nonsquare in an arbitrary number field. -/
theorem padicSquareNonsquare : PadicSquareNonsquareStatement.{u} := by
  classical
  intro p hp K hK hNK positive
  let : NeZero (4 * p) := ⟨Nat.mul_ne_zero (by norm_num) hp.out.ne_zero⟩
  cases positive with
  | false =>
    have hinf := Nat.infinite_setOfPred_prime_and_eq_mod
      (q := 4 * p) (a := -1) (by exact isUnit_one.neg)
    obtain ⟨q, ⟨⟨hq, hres⟩, hbad⟩⟩ :=
      (hinf.sdiff (finite_signedPrimes_square_in_numberField K (-1) (by norm_num))).nonempty
    refine ⟨-(q : ℚ), ?_, ?_, ?_⟩
    · simpa using (neg_neg_of_pos (Nat.cast_pos.mpr hq.pos) : -(q : ℚ) < 0)
    · have hcong : ((-(q : ℤ) : ℤ) : ZMod (4 * p)) = (1 : ℤ) := by
        simpa using congrArg Neg.neg hres
      have hdiv : (4 * p : ℤ) ∣ 1 - -(q : ℤ) := by
        simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub (-(q : ℤ)) 1 (4 * p)).mp hcong
      simpa using padic_isSquare_of_congruent_one p (-(q : ℤ)) hdiv
    · intro h
      exact hbad ⟨hq, by simpa using h⟩
  | true =>
    have hinf := Nat.infinite_setOfPred_prime_and_eq_mod
      (q := 4 * p) (a := 1) isUnit_one
    obtain ⟨q, ⟨⟨hq, hres⟩, hbad⟩⟩ :=
      (hinf.sdiff (finite_signedPrimes_square_in_numberField K 1 (by norm_num))).nonempty
    refine ⟨(q : ℚ), ?_, ?_, ?_⟩
    · simpa using (Nat.cast_pos.mpr hq.pos : (0 : ℚ) < q)
    · have hcong : ((q : ℤ) : ZMod (4 * p)) = (1 : ℤ) := by simpa using hres
      have hdiv : (4 * p : ℤ) ∣ 1 - (q : ℤ) := by
        simpa using (ZMod.intCast_eq_intCast_iff_dvd_sub (q : ℤ) 1 (4 * p)).mp hcong
      simpa using padic_isSquare_of_congruent_one p (q : ℤ) hdiv
    · intro h
      exact hbad ⟨hq, by simpa using h⟩

end Langlands.Global
