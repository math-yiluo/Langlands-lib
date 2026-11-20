import Langlands.Global.Arithmetic.CyclicHasseNorm
import Mathlib.Data.Int.GCD

/-! # Descent of norms modulo powers -/

noncomputable section

universe u

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField.LiesOver Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.Global

open AdelicFunctoriality Langlands.LocalClassField

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- A base-field unit is congruent to a norm of an extension-field unit modulo powers. -/
def IsNormMulPower (n : ℕ) (a : Fˣ) : Prop :=
  ∃ (b : Eˣ) (q : Fˣ), normUnits F E b * q ^ n = a

private theorem normUnits_base (q : Fˣ) :
    normUnits F E (Units.map (algebraMap F E) q) = q ^ Module.finrank F E := by
  apply Units.ext
  exact Algebra.norm_algebraMap _

/-- Coprimality of the power and the extension degree makes every unit a norm modulo powers. -/
theorem isNormMulPower_of_coprime (n : ℕ) (h : (Module.finrank F E).Coprime n) (a : Fˣ) :
    IsNormMulPower (E := E) n a := by
  let d := Module.finrank F E
  let x := Nat.gcdA d n
  let y := Nat.gcdB d n
  have hbez : (d : ℤ) * x + n * y = 1 := by
    have h' := Nat.gcd_eq_gcd_ab d n
    rw [show d.gcd n = 1 from h, Nat.cast_one] at h'
    exact h'.symm
  refine ⟨Units.map (algebraMap F E) (a ^ x), a ^ y, ?_⟩
  rw [normUnits_base, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm x, mul_comm y, ← zpow_add, hbez, zpow_one]

/-- When the extension degree divides the power, a norm modulo powers is already a norm. -/
theorem IsNormMulPower.mem_normSubgroup {n : ℕ} {a : Fˣ}
    (h : IsNormMulPower (E := E) n a) (hn : Module.finrank F E ∣ n) :
    a ∈ normSubgroup F E := by
  obtain ⟨c, q, rfl⟩ := h
  obtain ⟨m, hm⟩ := hn
  refine ⟨c * Units.map (algebraMap F E) (q ^ m), ?_⟩
  change normUnits F E (c * Units.map (algebraMap F E) (q ^ m)) = normUnits F E c * q ^ n
  rw [map_mul, normUnits_base, ← pow_mul, hm, mul_comm m]

/-- Every finite local degree in a finite Galois extension divides the global degree. -/
theorem finiteCompletion_finrank_dvd [NumberField F] [NumberField E] [IsGalois F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion F) (w.adicCompletion E) ∣ Module.finrank F E := by
  let : FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) := FiniteExtension.local_finite v w
  let : IsGalois (v.adicCompletion F) (w.adicCompletion E) := isGalois_adicCompletion v w
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  let f := ClassField.Global.FundamentalClass.decompositionHom v w
  rw [Nat.card_congr (MonoidHom.ofInjective (ClassField.Global.decompositionHom_injective v w)).toEquiv]
  exact Subgroup.card_subgroup_dvd_card f.range

/-- Norms modulo powers over a quadratic number-field extension descend from the actual
norms modulo powers at all pairs of places. -/
def NumberFieldQuadraticNormPowerDescentStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
    [FiniteDimensional F E], Module.finrank F E = 2 →
    ∀ (n : ℕ) (a : Fˣ),
    (∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
      IsNormMulPower (F := v.adicCompletion F) (E := w.adicCompletion E) n (Units.map (algebraMap F (v.adicCompletion F)) a)) →
    (∀ (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v],
      IsNormMulPower (F := v.Completion) (E := w.Completion) n (Units.map (algebraMap F v.Completion) a)) →
    IsNormMulPower (E := E) n a

/-- Coprimality handles odd powers, while even powers reduce to the cyclic Hasse norm theorem. -/
theorem numberFieldQuadraticNormPowerDescent : NumberFieldQuadraticNormPowerDescentStatement.{u} := by
  intro F E _ _ _ _ _ _ hdeg n a hfin hinf
  by_cases hdiv : 2 ∣ n
  · let : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hdeg }
    let : IsGalois F E := inferInstance
    suffices hnorm : a ∈ normSubgroup F E by
      obtain ⟨b, hb⟩ := hnorm
      exact ⟨b, 1, by simpa only [one_pow, mul_one] using hb⟩
    apply cyclicNumberFieldHasseNorm F E a
    · intro v w hw
      have hdvd := finiteCompletion_finrank_dvd v w
      rw [hdeg] at hdvd
      exact (hfin v w).mem_normSubgroup (hdvd.trans hdiv)
    · intro v w hw
      have hdvd : Module.finrank v.Completion w.Completion ∣ 2 := by
        rcases w.isUnramified_or_isRamified F with h | h
        · rw [h.finrank_eq_one v]
          exact one_dvd _
        · rw [h.finrank_eq_two v]
      exact (hinf v w).mem_normSubgroup (hdvd.trans hdiv)
  · apply isNormMulPower_of_coprime
    rw [hdeg]
    exact Nat.prime_two.coprime_iff_not_dvd.mpr hdiv

end Langlands.Global
