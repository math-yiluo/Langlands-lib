import Langlands.ClassField.Global.PrincipalIdeleDivisorStatement

/-! # Principal ideles have the divisor of their principal fractional ideal -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField nonZeroDivisors

variable {E : Type u} [Field E] [NumberField E]

private theorem valuation_eq_exp_neg_count_spanSingleton
    (w : HeightOneSpectrum (𝓞 E)) (a : E) (ha : a ≠ 0) :
    w.valuation E a = WithZero.exp
      (-FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ a)) := by
  obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq (𝓞 E)⁰ a
  have hn : n ≠ 0 := by
    intro hn
    apply ha
    rw [hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hI : FractionalIdeal.spanSingleton (𝓞 E)⁰ (IsLocalization.mk' E n d) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha
  have hrepr : FractionalIdeal.spanSingleton (𝓞 E)⁰ (IsLocalization.mk' E n d) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((algebraMap (𝓞 E) E) d)⁻¹ *
        ↑(Ideal.span {n} : Ideal (𝓞 E)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined E w hI hrepr, valuation_of_mk',
    intValuation_if_neg _ hn, intValuation_if_neg _ (nonZeroDivisors.coe_ne_zero d),
    ← WithZero.exp_sub]
  congr 1
  ring

/-- The actual principal idele has the prime multiplicities of its principal fractional ideal. -/
theorem principalIdeleDivisorFormula : PrincipalIdeleDivisorFormula.{u} := by
  intro E _ _ w a
  have hv := valued_units w (ideleCoordinate w (IdeleGroup.unitEmbedding (𝓞 E) E a))
  rw [ideleCoordinate_unitEmbedding] at hv
  have hc : Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (a : E) := by
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
      using (valuedAdicCompletion_eq_valuation' (v := w) (a : E))
  rw [hc,
    valuation_eq_exp_neg_count_spanSingleton w (a : E) (Units.ne_zero a)] at hv
  have h := WithZero.exp_injective hv
  change -Multiplicative.toAdd
    (unitsExponent w (ideleCoordinate w (IdeleGroup.unitEmbedding (𝓞 E) E a))) = _
  linarith

end Langlands.ClassField.Global
