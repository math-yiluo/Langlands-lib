import Langlands.Galois.PureEulerComparison
import Langlands.Galois.FrobeniusCharacter
import Langlands.Global.Arithmetic.ChebotarevPrimeRealizationProof
import Langlands.Global.FiniteAdeleSplit
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-! # Parity of pure weight differences -/

noncomputable section

namespace Langlands.GaloisRepresentation

open Cohomology.Weights Langlands.Global Langlands.Unramified Polynomial Filter
open scoped NumberField Valued

private theorem not_isSquare_natCast_of_not_dvd_discr
    {E : Type*} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (hdiscr : ¬ (p : ℤ) ∣ NumberField.discr E) :
    ¬ IsSquare (p : E) := by
  rw [isSquare_iff_exists_sq]
  rintro ⟨x, hx⟩
  have hxint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (show 0 < 2 by decide)
    rw [← hx]
    exact isIntegral_natCast p
  let y : 𝓞 E := ⟨x, hxint⟩
  have hy : y ^ 2 = (p : 𝓞 E) := by
    apply Subtype.ext
    exact hx.symm
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : P.IsMaximal := (Nat.prime_iff_prime_int.mp hp).isMaximal_span_singleton
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) P
  have : Q.IsMaximal := hQ
  have : Q.LiesOver P := hQP
  have hmap : P.map (algebraMap ℤ (𝓞 E)) = Ideal.span {(p : 𝓞 E)} := by
    simp [P, Ideal.map_span]
  have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (Q.over_def P).le
  have hpQ : (p : 𝓞 E) ∈ Q := by
    apply (Ideal.span_singleton_le_iff_mem _).mp
    exact hmap ▸ hle
  have hQ2 : P.map (algebraMap ℤ (𝓞 E)) ≤ Q ^ 2 := by
    rw [hmap, Ideal.span_singleton_le_iff_mem, ← hy]
    have hyQ : y ∈ Q := hQ.isPrime.mem_of_pow_mem 2 (hy ▸ hpQ)
    rw [pow_two, pow_two]
    exact Ideal.mul_mem_mul hyQ hyQ
  have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  let : Algebra.IsUnramifiedAt ℤ Q :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E)
      (Nat.prime_iff_prime_int.mp hp)).mp hdiscr Q inferInstance (by simpa using hpQ)
  have hram : P.ramificationIdx' Q = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx' P Q hmap0]
    exact Ideal.ramificationIdx_eq_one Q ℤ
  exact (Ideal.ramificationIdx'_ne_one_iff hle).mpr hQ2 hram

/-- At a rational prime away from the coefficient discriminant, the pure
    radius can lie in the coefficient field only for an even weight. -/
theorem exists_int_of_radius_mem_numberField (E : IntermediateField ℚ ℂ) [NumberField E]
    {p : ℕ} (hp : p.Prime) (hdiscr : ¬ (p : ℤ) ∣ NumberField.discr E)
    {d : ℤ} (h : (radius p d : ℂ) ∈ E) :
    ∃ k : ℤ, d = 2 * k := by
  let k := d / 2
  refine ⟨k, ?_⟩
  by_contra hne
  have hd : d = 2 * k + 1 := by dsimp [k] at *; omega
  have hhalf : (d : ℝ) / 2 = (k : ℝ) + 1 / 2 := by
    rw [hd]
    push_cast
    ring
  have hpos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hradius : (radius p d : ℂ) = (p : ℂ) ^ k * (Real.sqrt p : ℂ) := by
    rw [radius, hhalf, Real.rpow_add hpos, Real.rpow_intCast, ← Real.sqrt_eq_rpow,
      Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_natCast]
  have hsqrt : (Real.sqrt p : ℂ) ∈ E := by
    have hv := E.div_mem h (E.toSubfield.zpow_mem (E.natCast_mem p) k)
    rwa [hradius, mul_comm, mul_div_cancel_right₀ _
      (zpow_ne_zero k (Nat.cast_ne_zero.mpr hp.ne_zero))] at hv
  apply not_isSquare_natCast_of_not_dvd_discr hp hdiscr
  refine (isSquare_iff_exists_sq _).mpr ⟨⟨_, hsqrt⟩, ?_⟩
  apply Subtype.ext
  change (p : ℂ) = (Real.sqrt p : ℂ) ^ 2
  rw [← Complex.ofReal_pow, Real.sq_sqrt hpos.le, Complex.ofReal_natCast]

theorem radius_two_mul (q : ℕ) (k : ℤ) : radius q (2 * k) = (q : ℝ) ^ k := by
  have h : (((2 * k : ℤ) : ℝ) / 2) = (k : ℝ) := by push_cast; ring
  rw [radius, h, Real.rpow_intCast]

section FinitePlaces

universe uK uL uM uV uW

variable {K : Type uK} [Field K] [NumberField K]

theorem residueCharacteristic_prime (v : FinitePlace K) : (residueCharacteristic v).Prime :=
  CharP.prime_ringChar (𝓞 K ⧸ v.asIdeal)

theorem residueCharacteristic_eq_of_prime_card {v : FinitePlace K}
    (hp : (residueCardinality v).Prime) : residueCharacteristic v = residueCardinality v := by
  let R := 𝓞 K ⧸ v.asIdeal
  let : Fintype R := Fintype.ofFinite R
  let : Fact (ringChar R).Prime := ⟨residueCharacteristic_prime v⟩
  apply (Nat.prime_dvd_prime_iff_eq (residueCharacteristic_prime v) hp).mp
  change ringChar R ∣ Nat.card R
  rw [Nat.card_eq_fintype_card]
  exact (prime_dvd_char_iff_dvd_card (R := R) (ringChar R)).mp dvd_rfl

/-- A nonzero integer is prime to the residue characteristic outside
    a finite set of places. -/
theorem eventually_residueCharacteristic_not_dvd (a : ℕ) (ha : a ≠ 0) :
    ∀ᶠ v : FinitePlace K in cofinite, ¬ residueCharacteristic v ∣ a := by
  have hf : {v : FinitePlace K | (a : 𝓞 K) ∈ v.asIdeal}.Finite :=
    Set.finite_coe_iff.mp (finite_natCast_mem_asIdeal K a ha)
  apply Filter.eventually_cofinite.mpr
  simp only [not_not]
  refine hf.subset ?_
  intro v hv
  change (a : 𝓞 K) ∈ v.asIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (CharP.cast_eq_zero_iff (𝓞 K ⧸ v.asIdeal) (residueCharacteristic v) a).mpr hv

private theorem exists_degreeOne_nonzero_trace {D : Type uM} [Field D] [CharZero D]
    [TopologicalSpace D] [IsTopologicalRing D] [T2Space D] (A : Objects.{uK, uM, uW} K D)
    (hA : 0 < A.val.rank) (S : Finset (FinitePlace K)) :
    ∃ v : FinitePlace K, v ∉ S ∧ (residueCardinality v).Prime ∧
      A.val.representation.character (globalGeometricFrobenius v) ≠ 0 := by
  by_contra! h
  have heq := eq_of_continuous_of_globalGeometricFrobenius_eq S (continuous_character A)
    (continuous_const : Continuous fun _ : Field.absoluteGaloisGroup K => (0 : D))
    (fun t g => Representation.char_conj A.val.representation g t) (fun _ _ => rfl) h
  have hid := congrFun heq 1
  rw [Representation.char_one] at hid
  exact (Nat.cast_ne_zero.mpr hA.ne') hid

/-- Two pure families weakly associated to the same numerical spectrum have
    weights differing by an even integer when a chosen member of the second
    family has positive rank and the first family has a chosen member. -/
def PureWeightDifferenceEvenStatement : Prop :=
  ∀ {K : Type uK} [Field K] [NumberField K]
    {L : Type uL} [Field L] [NumberField L] {M : Type uM} [Field M] [NumberField M]
    {excludedL : Finset (FinitePlace L)} {excludedM : Finset (FinitePlace M)}
    {R : Collection.{uK, uL, uV} K L excludedL} {U : Collection.{uK, uM, uW} K M excludedM}
    {ι : L →+* ℂ} {κ : M →+* ℂ} {r : ℕ} {s : SpectralSystem (FinitePlace K) r}
    {m n : ℤ} (_lam : {lam : FinitePlace L // lam ∉ excludedL})
    (mu : {mu : FinitePlace M // mu ∉ excludedM}),
    0 < (U mu).val.rank →
    IsPureCompatible excludedL R m → IsPureCompatible excludedM U n →
    IsWeaklyAssociatedToSpectrum ι excludedL R s →
    IsWeaklyAssociatedToSpectrum κ excludedM U s →
    ∃ k : ℤ, m - n = 2 * k

theorem pureWeightDifferenceEven : PureWeightDifferenceEvenStatement.{uK, uL, uM, uV, uW} := by
  classical
  intro K _ _ L _ _ M _ _ excludedL excludedM R U ι κ r s m n lam mu hr hR hU hs ht
  obtain ⟨A, P, hP, hPm⟩ := hR
  obtain ⟨B, Q, hQ, hQn⟩ := hU
  let ι₀ : L →ₐ[ℚ] ℂ := ⟨ι, map_ratCast ι⟩
  let κ₀ : M →ₐ[ℚ] ℂ := ⟨κ, map_ratCast κ⟩
  let : FiniteDimensional ℚ ι₀.fieldRange :=
    LinearEquiv.finiteDimensional ι₀.equivFieldRange.toLinearEquiv
  let : FiniteDimensional ℚ κ₀.fieldRange :=
    LinearEquiv.finiteDimensional κ₀.equivFieldRange.toLinearEquiv
  let E := ι₀.fieldRange ⊔ κ₀.fieldRange
  let : NumberField E := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hcomp := eventually_pureEuler_eq_comp_of_weakAssociation hs ht hP hQ hPm hQn lam mu
  let good (v : FinitePlace K) :=
    v ∉ B ∧ residueCharacteristic v ≠ residueCharacteristic lam.val ∧
      residueCharacteristic v ≠ residueCharacteristic mu.val ∧
      ¬ residueCharacteristic v ∣ (NumberField.discr E).natAbs ∧
      (P v).map ι = ((Q v).map κ).comp (C (radius (residueCardinality v) (m - n) : ℂ) * X)
  have hgood : ∀ᶠ v in cofinite, good v := by
    filter_upwards [B.eventually_cofinite_notMem, hcomp,
      eventually_residueCharacteristic_not_dvd (K := K) (residueCharacteristic lam.val)
        (residueCharacteristic_prime lam.val).ne_zero,
      eventually_residueCharacteristic_not_dvd (K := K) (residueCharacteristic mu.val)
        (residueCharacteristic_prime mu.val).ne_zero,
      eventually_residueCharacteristic_not_dvd (K := K) (NumberField.discr E).natAbs
        (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E))] with v hv h hl hm hd
    have hL : residueCharacteristic v ≠ residueCharacteristic lam.val :=
      fun e => hl (e ▸ dvd_rfl)
    have hM : residueCharacteristic v ≠ residueCharacteristic mu.val :=
      fun e => hm (e ▸ dvd_rfl)
    exact ⟨hv, hL, hM, hd, h hL hM⟩
  let S := (Filter.eventually_cofinite.mp hgood).toFinset
  let : CharZero (FiniteCompletion M mu.val) :=
    Algebra.charZero_of_charZero M (FiniteCompletion M mu.val)
  obtain ⟨w, hw, hp, htr⟩ := exists_degreeOne_nonzero_trace (U mu) hr S
  have hwgood : good w := by
    by_contra hbad
    exact hw ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr hbad)
  rcases hwgood with ⟨hB, _, hμ, hdisc, heq⟩
  have hQcoeff : (Q w).coeff 1 ≠ 0 := by
    intro hz
    apply htr
    have hmatch : eulerPolynomial (U mu) (globalGeometricFrobenius w) =
        (Q w).map (NumberField.FinitePlace.embedding mu.val) :=
      (hasEulerPolynomialAt_iff.mp (hQ mu w hB hμ)).2
    have hc := congrArg (fun P => P.coeff 1) hmatch
    rw [coeff_one_eulerPolynomial, coeff_map, hz, map_zero, neg_eq_zero] at hc
    exact hc
  have hκcoeff : κ ((Q w).coeff 1) ≠ 0 := (_root_.map_ne_zero κ).mpr hQcoeff
  have hlinear :
      ι ((P w).coeff 1) = κ ((Q w).coeff 1) * (radius (residueCardinality w) (m - n) : ℂ) := by
    simpa only [coeff_map, comp_C_mul_X_coeff, pow_one] using
      congrArg (fun P => P.coeff 1) heq
  have hratio : ι ((P w).coeff 1) / κ ((Q w).coeff 1) =
      (radius (residueCardinality w) (m - n) : ℂ) :=
    (div_eq_iff hκcoeff).2 (hlinear.trans (mul_comm _ _))
  have hE : (radius (residueCardinality w) (m - n) : ℂ) ∈ E := hratio ▸ E.div_mem
    ((le_sup_left : ι₀.fieldRange ≤ E) (AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩))
    ((le_sup_right : κ₀.fieldRange ≤ E) (AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩))
  refine exists_int_of_radius_mem_numberField E hp ?_ hE
  intro hdiv
  apply hdisc
  rw [residueCharacteristic_eq_of_prime_card hp]
  simpa using Int.natAbs_dvd_natAbs.mpr hdiv

end FinitePlaces
end Langlands.GaloisRepresentation
