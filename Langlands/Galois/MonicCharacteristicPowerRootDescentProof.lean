import Langlands.Galois.HarrisKottwitzPowerNormalizationStatement

/-!
# Descent of monic power roots in characteristic zero

This file proves `Langlands.GaloisRepresentation.MonicCharacteristicPowerRootDescentStatement`:
for a map of fields `ι : L →+* M` with `L` of characteristic zero, a positive integer `a`, a monic
`P ∈ M[X]` and `Q ∈ L[X]` with `Q.map ι = P ^ a`, there is a unique monic `R ∈ L[X]` with
`R.map ι = P` and `R ^ a = Q`.

The proof is an induction on the degree of `P`. Let `U` be the monic greatest common divisor of
`P` and its derivative `P'`. In characteristic zero the monic greatest common divisor of `P ^ a`
and its derivative `a P ^ (a - 1) P'` is `P ^ (a - 1) U`. Euclidean greatest common divisors,
derivatives, normalization and Euclidean division commute with `Polynomial.map ι`, so
`P / U = (Q / G).map ι` for the monic greatest common divisor `G` of `Q` and `Q'`, and
`U ^ a = (Q / (Q / G) ^ a).map ι`. The degree of `U` is less than that of `P`, because `U`
divides the nonzero `P'`. By induction `U` comes from `L[X]`, hence so does `P = (P / U) U`.
Monicity of the root and the identity `R ^ a = Q` follow from injectivity of `Polynomial.map ι`,
which also gives uniqueness.
-/

noncomputable section
set_option autoImplicit false

universe uL uW

namespace Langlands.GaloisRepresentation

open Polynomial

/-- For a monic polynomial `P` over a field of characteristic zero, the normalized Euclidean
greatest common divisor of `P ^ (b + 1)` and its derivative is `P ^ b` times the normalized
Euclidean greatest common divisor of `P` and its derivative. -/
theorem normalize_gcd_pow_succ_derivative {M : Type uW} [Field M] [CharZero M] [DecidableEq M]
    {P : M[X]} (hP : P.Monic) (b : ℕ) :
    normalize (EuclideanDomain.gcd (P ^ (b + 1)) (derivative (P ^ (b + 1)))) =
      P ^ b * normalize (EuclideanDomain.gcd P (derivative P)) := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hpow0 : P ^ (b + 1) ≠ 0 := pow_ne_zero _ hP0
  have hg0 : EuclideanDomain.gcd (P ^ (b + 1)) (derivative (P ^ (b + 1))) ≠ 0 := fun h =>
    hpow0 (EuclideanDomain.gcd_eq_zero_iff.1 h).1
  have hu0 : EuclideanDomain.gcd P (derivative P) ≠ 0 := fun h =>
    hP0 (EuclideanDomain.gcd_eq_zero_iff.1 h).1
  have hb : ((b : M) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
  have hc : C ((b : M) + 1) * C ((b : M) + 1)⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hb, C_1]
  apply eq_of_monic_of_associated (monic_normalize hg0)
    ((hP.pow b).mul (monic_normalize hu0))
  apply associated_of_dvd_dvd
  · -- the gcd of the power divides `P ^ b * gcd(P, P')`, by Bézout for `gcd(P, P')`
    rw [normalize_dvd_iff]
    refine dvd_trans ?_ (mul_dvd_mul_left (P ^ b) (associated_normalize _).dvd)
    have hbez : P ^ b * EuclideanDomain.gcd P (derivative P) =
        P ^ (b + 1) * EuclideanDomain.gcdA P (derivative P) +
          derivative (P ^ (b + 1)) *
            (C ((b : M) + 1)⁻¹ * EuclideanDomain.gcdB P (derivative P)) := by
      rw [EuclideanDomain.gcd_eq_gcd_ab, derivative_pow_succ]
      linear_combination
        (-(P ^ b * derivative P * EuclideanDomain.gcdB P (derivative P))) * hc
    rw [hbez]
    exact dvd_add ((EuclideanDomain.gcd_dvd_left _ _).mul_right _)
      ((EuclideanDomain.gcd_dvd_right _ _).mul_right _)
  · -- `P ^ b * gcd(P, P')` divides both `P ^ (b + 1)` and its derivative
    rw [dvd_normalize_iff]
    apply EuclideanDomain.dvd_gcd
    · rw [pow_succ]
      exact mul_dvd_mul_left _ (normalize_dvd_iff.2 (EuclideanDomain.gcd_dvd_left _ _))
    · rw [derivative_pow_succ, mul_assoc]
      exact (mul_dvd_mul_left _
        (normalize_dvd_iff.2 (EuclideanDomain.gcd_dvd_right _ _))).mul_left _

/-- The existence half of the descent, by induction on a strict bound `n` for the degree: a monic
polynomial whose positive power comes from `L[X]` comes from `L[X]` itself. -/
theorem exists_map_eq_of_map_eq_pow {L : Type uL} [Field L] [CharZero L] {M : Type uW} [Field M]
    (ι : L →+* M) {a : ℕ} (ha : 0 < a) :
    ∀ (n : ℕ) (P : M[X]) (Q : L[X]), P.natDegree < n → P.Monic → Q.map ι = P ^ a →
      ∃ R : L[X], R.map ι = P := by
  classical
  have : CharZero M := (RingHom.charZero_iff ι.injective).1 inferInstance
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  intro n
  induction n with
  | zero => intro P Q h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro P Q hdeg hP hQ
    by_cases h0 : P.natDegree = 0
    · rw [hP.natDegree_eq_zero] at h0
      exact ⟨1, by simp [h0]⟩
    have hP0 : P ≠ 0 := hP.ne_zero
    have hu0 : EuclideanDomain.gcd P (derivative P) ≠ 0 := fun h =>
      hP0 (EuclideanDomain.gcd_eq_zero_iff.1 h).1
    set U : M[X] := normalize (EuclideanDomain.gcd P (derivative P)) with hUdef
    have hUmonic : U.Monic := monic_normalize hu0
    have hU0 : U ≠ 0 := hUmonic.ne_zero
    have hUP : U ∣ P := normalize_dvd_iff.2 (EuclideanDomain.gcd_dvd_left _ _)
    have hUP' : U ∣ derivative P := normalize_dvd_iff.2 (EuclideanDomain.gcd_dvd_right _ _)
    have hP'0 : derivative P ≠ 0 := derivative_ne_zero.2 h0
    have hUdeg : U.natDegree < P.natDegree :=
      (natDegree_le_of_dvd hUP' hP'0).trans_lt (natDegree_derivative_lt h0)
    obtain ⟨T, hT⟩ := hUP
    have hT0 : T ≠ 0 := by
      rintro rfl
      exact hP0 (by rw [hT, mul_zero])
    -- the monic gcd of `Q` and `Q'` maps to `P ^ b * U`
    set G : L[X] := normalize (EuclideanDomain.gcd Q (derivative Q)) with hGdef
    have hG : G.map ι = P ^ b * U := by
      rw [hGdef, map_normalize, ← gcd_map, ← derivative_map, hQ, hUdef]
      exact normalize_gcd_pow_succ_derivative hP b
    -- `S = Q / G` maps to `T = P / U`
    have hS : (Q / G).map ι = T := by
      rw [Polynomial.map_div, hQ, hG]
      refine (EuclideanDomain.eq_div_of_mul_eq_right (mul_ne_zero (pow_ne_zero _ hP0) hU0) ?_).symm
      rw [pow_succ, mul_assoc, ← hT]
    -- `Q / S ^ (b + 1)` maps to `U ^ (b + 1)`
    have hQ₁ : (Q / (Q / G) ^ (b + 1)).map ι = U ^ (b + 1) := by
      rw [Polynomial.map_div, Polynomial.map_pow, hQ, hS]
      refine (EuclideanDomain.eq_div_of_mul_eq_right (pow_ne_zero _ hT0) ?_).symm
      rw [← mul_pow, mul_comm, ← hT]
    obtain ⟨V, hV⟩ := ih U _ (by omega) hUmonic hQ₁
    refine ⟨Q / G * V, ?_⟩
    rw [Polynomial.map_mul, hS, hV, hT, mul_comm]

/-- **Descent of monic power roots.** A monic polynomial over `M` whose positive power has
coefficients in the characteristic-zero subfield `ι(L)` has coefficients in `ι(L)`; its descent
to `L` is the unique monic root of the given polynomial over `L`. -/
theorem monicCharacteristicPowerRootDescent :
    MonicCharacteristicPowerRootDescentStatement.{uL, uW} := by
  intro L _ _ M _ ι a P Q ha hP hQ
  obtain ⟨R, hR⟩ :=
    exists_map_eq_of_map_eq_pow ι ha (P.natDegree + 1) P Q (Nat.lt_succ_self _) hP hQ
  refine ⟨R, ⟨?_, hR, ?_⟩, ?_⟩
  · rw [← monic_map_iff (f := ι), hR]
    exact hP
  · apply map_injective ι ι.injective
    rw [Polynomial.map_pow, hR, hQ]
  · rintro R' ⟨-, hR', -⟩
    apply map_injective ι ι.injective
    rw [hR', hR]

end Langlands.GaloisRepresentation
