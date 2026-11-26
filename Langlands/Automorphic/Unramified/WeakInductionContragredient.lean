import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # Contragredients of cuspidal weak inductions -/

noncomputable section

set_option autoImplicit false

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open CuspidalOperatorRealization Polynomial
open scoped NumberField

private theorem reverse_comp_X_pow (p : ℂ[X]) {f : ℕ} (hf : 0 < f) :
    (p.comp (X ^ f)).reverse = p.reverse.comp (X ^ f) := by
  apply Polynomial.funext
  intro x
  by_cases hx : x = 0
  · subst x
    have hdegree : ((X : ℂ[X]) ^ f).natDegree ≠ 0 := by
      rw [natDegree_X_pow]
      exact hf.ne'
    simp only [eval_comp, eval_pow, eval_X, zero_pow hf.ne', ← coeff_zero_eq_eval_zero,
      coeff_zero_reverse, leadingCoeff_comp hdegree, leadingCoeff_X_pow, one_pow, mul_one]
  · let : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
    let : Invertible (x⁻¹ ^ f) := invertibleOfNonzero (pow_ne_zero _ (inv_ne_zero hx))
    have h₁ := eval₂_reverse_mul_pow (RingHom.id ℂ) x⁻¹ (p.comp (X ^ f))
    have h₂ := eval₂_reverse_mul_pow (RingHom.id ℂ) (x⁻¹ ^ f) p
    simp only [invOf_eq_inv, inv_inv, eval₂_id, eval_comp, eval_pow, eval_X, natDegree_comp,
      natDegree_X_pow, inv_pow] at h₁
    simp only [invOf_eq_inv, inv_pow, inv_inv, eval₂_id, ← pow_mul, mul_comm f] at h₂
    rw [eval_comp, eval_pow, eval_X]
    exact mul_right_cancel₀ (inv_ne_zero (pow_ne_zero _ hx)) (h₁.trans h₂.symm)

private def normalizedReverse : ℂ[X] →* ℂ[X] where
  toFun p := C (p.leadingCoeff⁻¹) * p.reverse
  map_one' := by
    rw [← C_1, leadingCoeff_C, inv_one, reverse_C, C_1, one_mul]
  map_mul' p q := by
    simp only [leadingCoeff_mul, mul_inv, map_mul, reverse_mul_of_domain]
    ring

private theorem normalizedReverse_comp_X_pow (p : ℂ[X]) {f : ℕ} (hf : 0 < f) :
    normalizedReverse (p.comp (X ^ f)) = (normalizedReverse p).comp (X ^ f) := by
  have hdegree : ((X : ℂ[X]) ^ f).natDegree ≠ 0 := by
    rw [natDegree_X_pow]
    exact hf.ne'
  change C ((p.comp (X ^ f)).leadingCoeff⁻¹) * (p.comp (X ^ f)).reverse =
    (C (p.leadingCoeff⁻¹) * p.reverse).comp (X ^ f)
  rw [mul_comp, C_comp, reverse_comp_X_pow p hf, leadingCoeff_comp hdegree,
    leadingCoeff_X_pow, one_pow, mul_one]

private theorem normalizedReverse_eulerPolynomial {n : ℕ} (s : Eigenvalues n) :
    normalizedReverse s.eulerPolynomial = Eigenvalues.eulerPolynomial (s.map fun a => a⁻¹) := by
  have h := PairedHecke.C_mul_eulerPolynomial_map_inv s
  have hc := congrArg (fun p : ℂ[X] => p.eval 0) h
  rw [eval_mul, eval_C, Eigenvalues.eulerPolynomial_eval_zero, mul_one,
    ← coeff_zero_eq_eval_zero, coeff_zero_reverse] at hc
  change C (s.eulerPolynomial.leadingCoeff⁻¹) * s.eulerPolynomial.reverse = _
  rw [← h, ← mul_assoc, ← map_mul, hc, inv_mul_cancel₀
    (leadingCoeff_ne_zero.mpr (Eigenvalues.eulerPolynomial_ne_zero s)), map_one, one_mul]

/-- Passing both actual cuspidal realizations to contragredients preserves the
cuspidal weak-induction relation. -/
def WeakInductionContragredientStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    {r m : ℕ} (S Sd : CuspidalOperatorRealization F r) (T Td : CuspidalOperatorRealization E m)
    (Pd : CuspidalSpectralPresentation.{uF, uV} Sd) (Qd : CuspidalSpectralPresentation.{uE, uW} Td),
    Sd.realization.IsContragredientOf S.realization →
    Td.realization.IsContragredientOf T.realization →
    S.isoClass.IsWeakInductionOf.{uF, uE, uV, uW} T.isoClass →
    Pd.spectralSystem.IsArithmeticWeakInductionOf Qd.spectralSystem

set_option maxHeartbeats 500000 in
/-- Inverting the Satake spectra takes normalized reverses, and this
operation preserves the induction product with every residue-degree substitution. -/
theorem weakInductionContragredient : WeakInductionContragredientStatement.{uF, uE, uV, uW} := by
  intro F E _ _ _ _ _ _ _ r m S Sd T Td Pd Qd hSd hTd h
  obtain ⟨P, Q, hPQ⟩ := (IsoClass.isWeakInductionOf_isoClass_iff S T).mp h
  refine ⟨hPQ.1, ?_⟩
  filter_upwards [hPQ.2, Pd.exceptional.eventually_cofinite_notMem,
    SpectralSystem.eventually_avoidsAbove (F := F) Qd.exceptional] with v hgood hv hAbove
  obtain ⟨hP, hQ, he, hEuler⟩ := hgood
  refine ⟨hv, hAbove, he, ?_⟩
  have h1 : Pd.spectralSystem.eulerPolynomial v hv =
      normalizedReverse (P.spectralSystem.eulerPolynomial v hP) := by
    change (Pd.spectralSystem.eigenvalues v hv).eulerPolynomial = _
    rw [eigenvalues_eq_map_inv_of_isContragredientOf S Sd P Pd hSd v hP hv,
      SpectralSystem.eulerPolynomial, normalizedReverse_eulerPolynomial]
  have h2 (w : FinitePlacesAbove E v) : Qd.spectralSystem.eulerPolynomial w.1 (hAbove w) =
      normalizedReverse (Q.spectralSystem.eulerPolynomial w.1 (hQ w)) := by
    change (Qd.spectralSystem.eigenvalues w.1 (hAbove w)).eulerPolynomial = _
    rw [eigenvalues_eq_map_inv_of_isContragredientOf T Td Q Qd hTd w.1 (hQ w) (hAbove w),
      SpectralSystem.eulerPolynomial, normalizedReverse_eulerPolynomial]
  rw [h1, hEuler]
  unfold SpectralSystem.inducedEulerPolynomial
  rw [map_prod]
  exact Finset.prod_congr rfl fun w _ => by
    rw [h2 w, normalizedReverse_comp_X_pow _ (w.1.asIdeal.inertiaDeg_pos (𝓞 F))]

end Langlands.Automorphic.Unramified
