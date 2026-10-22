import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # Auxiliary cyclotomic extensions of number fields

For a number field `F` and `n > 0`, a prime `q ≡ 1 (mod n · [F : ℚ]!)` gives, inside the
cyclotomic field `F(ζ_q)`, a cyclic extension of `F` of degree `n`, and `F(ζ_q)` itself is
a Galois extension of `F` with a finite place whose ramification index is divisible by `n`.
-/

noncomputable section

namespace Langlands.Global

open NumberField IsDedekindDomain IntermediateField

universe u

/-- A prime `q` with `q ≡ 1 (mod max n 1 · [F : ℚ]!)`, chosen by `Classical.choose` from
Dirichlet's theorem for the modulus (Mathlib's `Nat.exists_prime_gt_modEq_one`). -/
def auxiliaryPrime (F : Type u) [Field F] [NumberField F] (n : ℕ) : ℕ :=
  Classical.choose (Nat.exists_prime_gt_modEq_one 0
    (Nat.mul_ne_zero (lt_of_lt_of_le Nat.one_pos (le_max_right n 1)).ne'
      (Nat.factorial_ne_zero (Module.finrank ℚ F))))

theorem auxiliaryPrime_prime (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    (auxiliaryPrime F n).Prime :=
  (Classical.choose_spec (Nat.exists_prime_gt_modEq_one 0
    (Nat.mul_ne_zero (lt_of_lt_of_le Nat.one_pos (le_max_right n 1)).ne'
      (Nat.factorial_ne_zero (Module.finrank ℚ F))))).1

/-- For `n > 0`, `n · [F : ℚ]!` divides `q - 1` for the auxiliary prime `q`. -/
theorem dvd_auxiliaryPrime_sub_one (F : Type u) [Field F] [NumberField F] {n : ℕ}
    (hn : 0 < n) : n * (Module.finrank ℚ F).factorial ∣ auxiliaryPrime F n - 1 := by
  have h : auxiliaryPrime F n ≡ 1 [MOD max n 1 * (Module.finrank ℚ F).factorial] :=
    (Classical.choose_spec (Nat.exists_prime_gt_modEq_one 0
      (Nat.mul_ne_zero (lt_of_lt_of_le Nat.one_pos (le_max_right n 1)).ne'
        (Nat.factorial_ne_zero (Module.finrank ℚ F))))).2.2
  rw [max_eq_left hn] at h
  exact (Nat.modEq_iff_dvd' (auxiliaryPrime_prime F n).one_le).1 h.symm

/-- A number field structure on an intermediate field of a number field extension. -/
theorem intermediateField_numberField {F : Type u} [Field F] [NumberField F] {M : Type u}
    [Field M] [NumberField M] [Algebra F M] (K : IntermediateField F M) : NumberField K :=
  { to_charZero := charZero_of_injective_algebraMap (algebraMap F K).injective
    to_finiteDimensional := Module.Finite.trans F K }

/-- In the cyclotomic field of a prime `q`, `q - 1` divides `[F : ℚ] · [F(ζ_q) : F]`. -/
theorem dvd_finrank_cyclotomicField (F : Type u) [Field F] [NumberField F] (q : ℕ)
    [hq : Fact q.Prime] :
    q - 1 ∣ Module.finrank ℚ F * Module.finrank F (CyclotomicField q F) := by
  let M := CyclotomicField q F
  let ζ : M := IsCyclotomicExtension.zeta q F M
  have hζ : IsPrimitiveRoot ζ q := IsCyclotomicExtension.zeta_spec q F M
  have hint : IsIntegral ℚ ζ := .of_finite ℚ ζ
  have h1 : Module.finrank ℚ ℚ⟮ζ⟯ = q - 1 := by
    rw [IntermediateField.adjoin.finrank hint, ← Polynomial.cyclotomic_eq_minpoly_rat hζ hq.out.pos,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime hq.out]
  rw [Module.finrank_mul_finrank ℚ F M, ← h1, ← Module.finrank_mul_finrank ℚ ℚ⟮ζ⟯ M]
  exact dvd_mul_right _ _

/-- Every number field has a cyclic Galois extension of every positive degree `n`, in the
same universe: a subfield of `F(ζ_q)` for the auxiliary prime `q`. -/
theorem exists_cyclic_extension (F : Type u) [Field F] [NumberField F] {n : ℕ} (hn : 0 < n) :
    ∃ (K : Type u) (_ : Field K) (_ : NumberField K) (_ : Algebra F K),
      IsGalois F K ∧ IsCyclic (K ≃ₐ[F] K) ∧ Module.finrank F K = n := by
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  set q := auxiliaryPrime F n
  have hq : q.Prime := auxiliaryPrime_prime F n
  have : Fact q.Prime := ⟨hq⟩
  let M := CyclotomicField q F
  have : IsGalois F M := IsCyclotomicExtension.isGalois {q} F M
  -- the Galois group is cyclic
  let ζ : M := IsCyclotomicExtension.zeta q F M
  have hζ : IsPrimitiveRoot ζ q := IsCyclotomicExtension.zeta_spec q F M
  have : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq
  have hcyc : IsCyclic (M ≃ₐ[F] M) :=
    isCyclic_of_injective (hζ.autToPow F) (hζ.autToPow_injective F)
  -- `n` divides `[M : F]`
  have hdvd : n ∣ Module.finrank F M := by
    have h1 : n * Module.finrank ℚ F ∣ q - 1 :=
      (mul_dvd_mul_left n (Nat.dvd_factorial hd le_rfl)).trans (dvd_auxiliaryPrime_sub_one F hn)
    have h2 := h1.trans (dvd_finrank_cyclotomicField F q)
    rw [mul_comm n] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hd h2
  -- the fixed field of the subgroup of order `[M : F] / n`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M ≃ₐ[F] M)
  have hog : orderOf g = Module.finrank F M := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, IsGalois.card_aut_eq_finrank]
  let H : Subgroup (M ≃ₐ[F] M) := Subgroup.zpowers (g ^ n)
  have : IsMulCommutative (M ≃ₐ[F] M) := inferInstance
  have hH : H.Normal := Subgroup.normal_of_isMulCommutative H
  have hcardH : Nat.card H = Module.finrank F M / n := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hn.ne' (hog ▸ hdvd), hog]
  let K := IntermediateField.fixedField H
  have : NumberField K := intermediateField_numberField K
  have hKM : Module.finrank K M = Module.finrank F M / n := by
    rw [IntermediateField.finrank_fixedField_eq_card, hcardH]
  have hpos : 0 < Module.finrank F M := Module.finrank_pos
  have hK : Module.finrank F K = n := by
    have h := Module.finrank_mul_finrank F K M
    rw [hKM] at h
    have hq' : 0 < Module.finrank F M / n := Nat.div_pos (Nat.le_of_dvd hpos hdvd) hn
    apply Nat.eq_of_mul_eq_mul_right hq'
    rw [h, Nat.mul_div_cancel' hdvd]
  have : IsGalois F K := IsGalois.of_fixedField_normal_subgroup H
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hK⟩
  exact isCyclic_of_surjective (AlgEquiv.restrictNormalHom K)
    (AlgEquiv.restrictNormalHom_surjective M)

/-- The ramification index over `ℤ` of a prime of a number field is at most its degree. -/
theorem ramificationIdx_int_le_finrank {F : Type u} [Field F] [NumberField F] (q : ℕ)
    [hq : Fact q.Prime] (P : Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})] :
    P.ramificationIdx ℤ ≤ Module.finrank ℚ F := by
  classical
  have : (Ideal.span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  have h := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(q : ℤ)}) (𝓞 F)
  rw [RingOfIntegers.rank] at h
  rw [← h]
  calc P.ramificationIdx ℤ ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
        Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos P ℤ)
    _ ≤ _ := Finset.single_le_sum
        (f := fun Q : (Ideal.span {(q : ℤ)}).primesOver (𝓞 F) =>
          Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨P, ‹_›, ‹_›⟩)

/-- A prime above `q` in a number field containing a primitive `q`-th root of unity has
ramification index over `ℤ` divisible by `q - 1`. -/
theorem sub_one_dvd_ramificationIdx {K : Type u} [Field K] [NumberField K] (q : ℕ)
    [hq : Fact q.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ q) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    q - 1 ∣ P.ramificationIdx ℤ := by
  have : NeZero q := ⟨hq.out.ne_zero⟩
  have : IsCyclotomicExtension {q} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let P₀ : Ideal (𝓞 ℚ⟮ζ⟯) := P.under (𝓞 ℚ⟮ζ⟯)
  have : P.LiesOver P₀ := ⟨rfl⟩
  have : P₀.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.tower_bot P P₀ _
  rw [Ideal.ramificationIdx_tower (R := ℤ) P₀ P,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime q ℚ⟮ζ⟯ P₀]
  exact dvd_mul_right _ _

/-- Every number field `F` has a finite Galois extension `K` with a finite place whose
ramification index over `F` is divisible by a given `n > 0`: the cyclotomic field `F(ζ_q)`
for the auxiliary prime `q ≡ 1 (mod n · [F : ℚ]!)`. -/
theorem exists_galois_ramified (F : Type u) [Field F] [NumberField F] (n : ℕ) (hn : 0 < n) :
    ∃ (K : Type u) (_ : Field K) (_ : NumberField K) (_ : Algebra F K), IsGalois F K ∧
      ∃ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)),
        w.asIdeal.LiesOver v.asIdeal ∧ n ∣ w.asIdeal.ramificationIdx (𝓞 F) := by
  classical
  set d := Module.finrank ℚ F
  set q := auxiliaryPrime F n
  have hq : q.Prime := auxiliaryPrime_prime F n
  have : Fact q.Prime := ⟨hq⟩
  let K := CyclotomicField q F
  have : IsGalois F K := IsCyclotomicExtension.isGalois {q} F K
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta q F K) q :=
    IsCyclotomicExtension.zeta_spec q F K
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  have : p.IsMaximal := Int.ideal_span_isMaximal_of_prime q
  have hp0 : p ≠ ⊥ := by simp [p, hq.ne_zero]
  obtain ⟨⟨Q, hQ, hQo⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) p
  let P : Ideal (𝓞 F) := Q.under (𝓞 F)
  have : Q.LiesOver P := ⟨rfl⟩
  have : P.LiesOver p := Ideal.LiesOver.tower_bot Q P p
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨P, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩,
    ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q⟩, ‹_›, ?_⟩
  change n ∣ Q.ramificationIdx (𝓞 F)
  have h1 : q - 1 ∣ Q.ramificationIdx ℤ := sub_one_dvd_ramificationIdx q hζ Q
  have h2 : Q.ramificationIdx ℤ = P.ramificationIdx ℤ * Q.ramificationIdx (𝓞 F) :=
    Ideal.ramificationIdx_tower P Q
  have h3 : P.ramificationIdx ℤ ∣ d.factorial :=
    Nat.dvd_factorial (Ideal.ramificationIdx_pos P ℤ) (ramificationIdx_int_le_finrank q P)
  have h4 : n * d.factorial ∣ q - 1 := dvd_auxiliaryPrime_sub_one F hn
  have h5 : d.factorial * n ∣ d.factorial * Q.ramificationIdx (𝓞 F) := by
    rw [mul_comm d.factorial n, mul_comm d.factorial]
    refine (h4.trans h1).trans ?_
    rw [h2, mul_comm]
    exact mul_dvd_mul_left _ h3
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos d) h5

end Langlands.Global
