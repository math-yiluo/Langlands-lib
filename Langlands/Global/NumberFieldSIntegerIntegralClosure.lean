import Langlands.Global.ArithmeticSIntegerExtension
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

noncomputable section

universe u

open IsDedekindDomain
open scoped NumberField

namespace Langlands.Global

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- Integrality in every original upper place implies integrality over the lower local ring. -/
theorem numberFieldPlace_isIntegral_of_forall_above (p : FinitePlace K) (x : L)
    (hx : ∀ q : FinitePlace L, q.asIdeal.LiesOver p.asIdeal → q.valuation L x ≤ 1) :
    IsIntegral (HeightOneSpectrum.valuationSubringAtPrime K p) x := by
  let V := HeightOneSpectrum.valuationSubringAtPrime K p
  let : Algebra V L := ((algebraMap K L).comp V.subtype).toAlgebra
  let : IsScalarTower V K L := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (𝓞 K) V L := .of_algebraMap_eq fun a => by
    exact IsScalarTower.algebraMap_apply (𝓞 K) K L a
  let C := integralClosure V L
  let : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  let : IsDedekindDomain C := integralClosure.isDedekindDomain V K L
  let : Algebra (𝓞 K) C := ((algebraMap V C).comp (algebraMap (𝓞 K) V)).toAlgebra
  let : IsScalarTower (𝓞 K) V C := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (𝓞 K) C L := .of_algebraMap_eq fun a => by
    exact IsScalarTower.algebraMap_apply (𝓞 K) K L a
  let f : (𝓞 L) →+* C :=
    (algebraMap (𝓞 L) L).codRestrict _ fun b =>
      ((Algebra.IsIntegral.isIntegral (R := 𝓞 K) b).algebraMap
        (B := L)).tower_top
  let : Algebra (𝓞 L) C := f.toAlgebra
  let : IsScalarTower (𝓞 L) C L := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (𝓞 K) (𝓞 L) C := .of_algebraMap_eq fun a => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L a
  have hlocal : x ∈ (⊥ : Subalgebra C L) := by
    rw [← HeightOneSpectrum.iInf_localization_eq_bot C, Algebra.mem_iInf]
    intro Q
    have hQV : Q.asIdeal.under V = IsLocalRing.maximalIdeal V :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V) Q.asIdeal)
    let : Q.asIdeal.LiesOver p.asIdeal := by
      constructor
      symm
      rw [← Ideal.under_under (A := 𝓞 K) (B := V) Q.asIdeal, hQV,
        IsLocalization.AtPrime.under_maximalIdeal V p.asIdeal]
    let q : FinitePlace L :=
      ⟨Q.asIdeal.under (𝓞 L), inferInstance,
        Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot _⟩
    have hq : q.asIdeal.LiesOver p.asIdeal := inferInstance
    have hle : HeightOneSpectrum.valuationSubringAtPrime L q ≤
        (Q.valuation L).valuationSubring := by
      rintro y ⟨a, b, hb, rfl⟩
      change Q.valuation L
        (algebraMap (𝓞 L) L a * (algebraMap (𝓞 L) L b)⁻¹) ≤ 1
      rw [map_mul, map_inv₀,
        IsScalarTower.algebraMap_apply (𝓞 L) C L b,
        (Q.valuation_eq_one_iff_notMem).mpr hb, inv_one, mul_one,
        IsScalarTower.algebraMap_apply (𝓞 L) C L a]
      exact Q.valuation_le_one _
    have heq : HeightOneSpectrum.valuationSubringAtPrime L q =
        (Q.valuation L).valuationSubring :=
      ValuationSubring.eq_of_le_of_ne_top _ hle (by
        simpa only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not] using
          (inferInstance : Q.valuation L |>.IsNontrivial))
    rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at heq
    change x ∈ HeightOneSpectrum.valuationSubringAtPrime L Q
    rw [← heq, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact hx q hq
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hlocal
  exact ha ▸ a.property

variable (S : Finset (FinitePlace K))

/-- Coefficients of the field minimal polynomial of an upper S-integer are lower S-integers. -/
theorem numberFieldSIntegers_minpoly_coeff_mem (x : L)
    (hx : x ∈ ((numberFieldExceptionalPreimage (L := L) S :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
    (n : ℕ) : (minpoly K x).coeff n ∈ (S : Set (FinitePlace K)).integer K := by
  intro p hp
  have hl : IsIntegral (HeightOneSpectrum.valuationSubringAtPrime K p) x :=
    numberFieldPlace_isIntegral_of_forall_above p x fun q hq => by
      let : q.asIdeal.LiesOver p.asIdeal := hq
      have hr : q.under (𝓞 K) = p := by
        apply HeightOneSpectrum.ext
        exact (Ideal.over_def q.asIdeal p.asIdeal).symm
      exact hx q (by simpa [hr] using hp)
  change (minpoly K x).coeff n ∈ (p.valuation K).valuationSubring
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hl, Polynomial.coeff_map]
  exact ((minpoly (HeightOneSpectrum.valuationSubringAtPrime K p) x).coeff n).property

/-- The upper S-integer ring at the full preimage equals the actual lower integral closure. -/
theorem numberFieldSIntegers_integralClosure_eq :
    (integralClosure ((S : Set (FinitePlace K)).integer K) L).toSubring =
      (((numberFieldExceptionalPreimage (L := L) S :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L).toSubring := by
  apply le_antisymm (numberFieldSIntegers_integralClosure_le S)
  intro x hx
  let R := (S : Set (FinitePlace K)).integer K
  have hlifts : minpoly K x ∈ Polynomial.lifts (algebraMap R K) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n =>
      ⟨⟨_, numberFieldSIntegers_minpoly_coeff_mem S x hx n⟩, rfl⟩
  obtain ⟨f, hf⟩ := (Polynomial.mem_lifts _).mp hlifts
  have hxK : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  refine ⟨f, Polynomial.monic_of_injective R.toSubring.subtype_injective
    (hf ▸ minpoly.monic hxK), ?_⟩
  change Polynomial.aeval x f = 0
  rw [← Polynomial.aeval_map_algebraMap K x, hf]
  exact minpoly.aeval K x

/-- Identify the original upper S-integers with the lower integral closure, fixing elements of L. -/
def numberFieldSIntegersIntegralClosureEquiv :
    integralClosure ((S : Set (FinitePlace K)).integer K) L ≃+*
      (((numberFieldExceptionalPreimage (L := L) S :
        Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) :=
  RingEquiv.subringCongr (numberFieldSIntegers_integralClosure_eq S)

@[simp]
theorem numberFieldSIntegersIntegralClosureEquiv_coe
    (x : integralClosure ((S : Set (FinitePlace K)).integer K) L) :
    (numberFieldSIntegersIntegralClosureEquiv S x : L) = x := rfl

end Langlands.Global
