import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Roots of units in a strictly Henselian local ring and units of `R[1/t]`

For a Henselian local ring `R` with separably closed residue field and a positive integer `m`
invertible in `R`, every unit of `R` is an `m`-th power and `R` contains a primitive
`m`-th root of unity. In any local ring with `m` invertible, an `m`-th root of unity that
maps to `1` in a nonzero ring is `1`.
For a domain `R` and a prime element `t`, every unit of `R[1/t]` is a unit of `R` times an
integer power of `t`.
-/

noncomputable section

open IsLocalRing Polynomial

namespace Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits

section Henselian

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- **Hensel lifting of simple roots of `X^m - u`.** If `m > 0` is invertible in a Henselian
local ring `R` and `u` is a unit, an `m`-th root of the residue of `u` lifts to an `m`-th
root of `u`. -/
theorem exists_pow_eq_lift {m : ℕ} (hm : IsUnit (m : R)) (hm0 : m ≠ 0) {u : R} (hu : IsUnit u)
    (a₀ : R) (ha₀ : residue R a₀ ^ m = residue R u) :
    ∃ w : R, w ^ m = u ∧ residue R w = residue R a₀ := by
  have hres : residue R (a₀ ^ m - u) = 0 := by
    rw [map_sub, map_pow, ha₀, sub_self]
  have hmem : a₀ ^ m - u ∈ maximalIdeal R := by
    rwa [← residue_eq_zero_iff]
  have ha₀u : IsUnit a₀ := by
    by_contra h
    have h0 : residue R a₀ = 0 := (residue_eq_zero_iff a₀).mpr ((mem_maximalIdeal a₀).mpr h)
    have hu0 : residue R u ≠ 0 := (hu.map (residue R)).ne_zero
    rw [h0, zero_pow hm0] at ha₀
    exact hu0 ha₀.symm
  obtain ⟨w, hw, hwa⟩ := HenselianLocalRing.is_henselian (X ^ m - C u)
    (monic_X_pow_sub_C u hm0) a₀ (by simpa using hmem) (by
      simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
        eval_pow, eval_X]
      exact hm.mul (ha₀u.pow _))
  refine ⟨w, ?_, ?_⟩
  · simpa [sub_eq_zero] using hw
  · rw [← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr hwa

variable [IsSepClosed (ResidueField R)]

/-- In a strictly Henselian local ring, every unit has an `m`-th root when `m > 0` is
invertible. -/
theorem exists_pow_eq_of_isUnit {m : ℕ} (hm : IsUnit (m : R)) (hm0 : m ≠ 0) {u : R}
    (hu : IsUnit u) : ∃ w : R, w ^ m = u := by
  have hmk : ((m : ResidueField R)) ≠ 0 := by
    simpa using (hm.map (residue R)).ne_zero
  have huk : residue R u ≠ 0 := (hu.map (residue R)).ne_zero
  obtain ⟨b, hb⟩ := IsSepClosed.exists_root (X ^ m - C (residue R u))
    (by
      rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hm0)]
      exact_mod_cast hm0)
    (separable_X_pow_sub_C _ hmk huk)
  obtain ⟨a₀, rfl⟩ := residue_surjective (R := R) b
  have ha₀ : residue R a₀ ^ m = residue R u := by
    simpa [sub_eq_zero] using hb
  obtain ⟨w, hw, -⟩ := exists_pow_eq_lift hm hm0 hu a₀ ha₀
  exact ⟨w, hw⟩

/-- A strictly Henselian local ring contains a primitive `m`-th root of unity for every positive
integer `m` invertible in it. -/
theorem exists_isPrimitiveRoot {m : ℕ} (hm : IsUnit (m : R)) (hm0 : m ≠ 0) :
    ∃ ζ : R, IsPrimitiveRoot ζ m := by
  have hmk : ((m : ResidueField R)) ≠ 0 := by
    simpa using (hm.map (residue R)).ne_zero
  have : NeZero ((m : ResidueField R)) := ⟨hmk⟩
  obtain ⟨b, hb⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (ResidueField R) m
  obtain ⟨a₀, rfl⟩ := residue_surjective (R := R) b
  have ha₀ : residue R a₀ ^ m = residue R 1 := by
    rw [map_one]
    exact hb.pow_eq_one
  obtain ⟨ζ, hζ, hζa⟩ := exists_pow_eq_lift hm hm0 isUnit_one a₀ ha₀
  refine ⟨ζ, IsPrimitiveRoot.mk_of_lt ζ (Nat.pos_of_ne_zero hm0) hζ ?_⟩
  intro l hl0 hlm hl
  have h := congrArg (residue R) hl
  rw [map_pow, map_one, hζa] at h
  exact absurd (hb.pow_eq_one_iff_dvd l |>.mp h) (Nat.not_dvd_of_pos_of_lt hl0 hlm)

end Henselian

section RootOfUnity

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- An `m`-th root of unity of a local ring, with `m` invertible, that is congruent to `1`
modulo the maximal ideal equals `1`. -/
theorem eq_one_of_pow_eq_one_of_sub_mem {m : ℕ} (hm : IsUnit (m : R)) {ζ : R}
    (hζ : ζ ^ m = 1) (hζ1 : ζ - 1 ∈ maximalIdeal R) : ζ = 1 := by
  have hres : residue R ζ = 1 := by
    rw [← sub_eq_zero, ← map_one (residue R), ← map_sub]
    exact (residue_eq_zero_iff _).mpr hζ1
  have hsum : IsUnit (∑ i ∈ Finset.range m, ζ ^ i) := by
    by_contra h
    have h0 : residue R (∑ i ∈ Finset.range m, ζ ^ i) = 0 :=
      (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr h)
    rw [map_sum] at h0
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at h0
    exact (hm.map (residue R)).ne_zero (by simpa using h0)
  have hgeom : (∑ i ∈ Finset.range m, ζ ^ i) * (ζ - 1) = 0 := by
    rw [geom_sum_mul, hζ, sub_self]
  have := (hsum.mul_right_eq_zero).mp hgeom
  exact sub_eq_zero.mp this

/-- An `m`-th root of unity of a local ring, with `m` invertible, whose image under a ring
homomorphism to a nontrivial ring is `1`, equals `1`. -/
theorem eq_one_of_pow_eq_one_of_map_eq_one {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) {m : ℕ} (hm : IsUnit (m : R)) {ζ : R} (hζ : ζ ^ m = 1) (hφ : φ ζ = 1) :
    ζ = 1 := by
  refine eq_one_of_pow_eq_one_of_sub_mem hm hζ ?_
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have := (h.map φ).ne_zero
  rw [map_sub, hφ, map_one, sub_self] at this
  exact this rfl

end RootOfUnity

section Away

variable {R : Type*} [CommRing R] [IsDomain R] {t : R}

/-- **Units of `R[1/t]`.** For a prime element `t` of a domain `R`, every unit of
`R[1/t]` is the image of a unit of `R` times an integer power of the image of `t`. -/
theorem exists_eq_unit_mul_zpow (ht : Prime t) (a : (Localization.Away t)ˣ) :
    ∃ (u : Rˣ) (k : ℤ), a = Units.map (algebraMap R (Localization.Away t)).toMonoidHom u *
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away t) t).unit ^ k := by
  have ht0 : t ≠ 0 := ht.ne_zero
  have hinj : Function.Injective (algebraMap R (Localization.Away t)) :=
    IsLocalization.injective (Localization.Away t)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  set T := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away t) t).unit with hTdef
  obtain ⟨⟨r, s₁⟩, hr⟩ := IsLocalization.surj (Submonoid.powers t) (a : Localization.Away t)
  obtain ⟨⟨r', s₂⟩, hr'⟩ :=
    IsLocalization.surj (Submonoid.powers t) ((a⁻¹ : (Localization.Away t)ˣ) : Localization.Away t)
  obtain ⟨i, hi⟩ := s₁.2
  obtain ⟨j, hj⟩ := s₂.2
  simp only at hr hr'
  rw [← hi] at hr
  rw [← hj] at hr'
  beta_reduce at hr hr'
  have hprod : r * r' = t ^ (i + j) := by
    apply hinj
    rw [map_mul, ← hr, ← hr', pow_add, map_mul]
    calc (a : Localization.Away t) * algebraMap R _ (t ^ i) *
          (((a⁻¹ : (Localization.Away t)ˣ) : Localization.Away t) * algebraMap R _ (t ^ j))
        = ((a : Localization.Away t) * ((a⁻¹ : (Localization.Away t)ˣ) : Localization.Away t)) *
            (algebraMap R _ (t ^ i) * algebraMap R _ (t ^ j)) := by
          ring
      _ = _ := by rw [Units.mul_inv, one_mul]
  obtain ⟨e, -, he⟩ := (dvd_prime_pow ht (i + j)).mp ⟨r', hprod.symm⟩
  obtain ⟨u, hu⟩ := he.symm
  refine ⟨u, (e : ℤ) - i, ?_⟩
  apply Units.ext
  have hT : ((T ^ ((e : ℤ) - i) : (Localization.Away t)ˣ) : Localization.Away t) *
      algebraMap R (Localization.Away t) t ^ i = algebraMap R (Localization.Away t) t ^ e := by
    have h1 : T ^ ((e : ℤ) - i) * T ^ i = T ^ e := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add, sub_add_cancel]
    have h2 := congrArg Units.val h1
    rwa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hTdef,
      IsUnit.unit_spec] at h2
  have hTi : IsUnit (algebraMap R (Localization.Away t) t ^ i) :=
    (IsLocalization.Away.algebraMap_isUnit t).pow i
  apply hTi.mul_left_injective
  simp only [Units.val_mul, Units.coe_map]
  rw [mul_assoc, hT, ← map_pow, hr, ← hu, map_mul, map_pow, mul_comm]
  rfl

end Away

end Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits
