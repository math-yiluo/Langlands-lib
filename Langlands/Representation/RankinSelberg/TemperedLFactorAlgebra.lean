import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.RankinSelberg.ReflectionRigidityProof
import Langlands.LocalFactor.ResidueReflection

/-!
Elementary normalization, divisibility and reflection reductions used in the
proof of JPSS Proposition 8.4. Analytic premises remain explicit in these lemmas.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

namespace TemperedLFactorAlgebra

/-- A normalized residual polynomial witnessing that `P` divides `B`. -/
structure NormalizedPolynomialQuotient (P B : ℂ[X]) where
  polynomial : ℂ[X]
  coeff_zero : polynomial.coeff 0 = 1
  factorization : B = polynomial * P

/-- Laurent divisibility preserves zero-freeness away from zero, and
normalization handles zero. -/
theorem poleFree_of_laurentDivisibility {P B R : ℂ[X]} {e : ℕ}
    (hP : P.coeff 0 = 1) (hdiv : X ^ e * B = R * P)
    (hB : ∀ z : ℂ, ‖z‖ < 1 → B.eval z ≠ 0) :
    ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0 := by
  intro z hz
  by_cases hzero : z = 0
  · subst z
    simpa only [← coeff_zero_eq_eval_zero, hP] using (one_ne_zero : (1 : ℂ) ≠ 0)
  · intro hroot
    have heval := congrArg (fun A : ℂ[X] => A.eval z) hdiv
    simp only [eval_mul, eval_pow, eval_X, hroot, mul_zero] at heval
    exact (mul_ne_zero (pow_ne_zero e hzero) (hB z hz)) heval

theorem doubleProduct_poleFree {k l : ℕ} {Q : Fin k → Fin l → ℂ[X]}
    (hQ : ∀ i j z, ‖z‖ < 1 → (Q i j).eval z ≠ 0) :
    ∀ z : ℂ, ‖z‖ < 1 → (∏ i, ∏ j, Q i j).eval z ≠ 0 := by
  intro z hz
  simp only [eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j _ => hQ i j z hz

/-- A normalized polynomial is relatively prime to the Laurent denominator.
The proof removes one factor of `X` at a time. -/
theorem quotient_of_laurentDivisibility {P B : ℂ[X]}
    (hP : P.coeff 0 = 1) (e : ℕ) (R : ℂ[X])
    (hdiv : X ^ e * B = R * P) : ∃ D : ℂ[X], B = D * P := by
  induction e generalizing R with
  | zero => exact ⟨R, by simpa only [pow_zero, one_mul] using hdiv⟩
  | succ e ih =>
    have hPeval : P.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero, hP]
    have hR : R.coeff 0 = 0 := by
      have heval := congrArg (fun A : ℂ[X] => A.eval 0) hdiv
      rw [coeff_zero_eq_eval_zero]
      simpa [hPeval] using heval.symm
    obtain ⟨S, rfl⟩ := X_dvd_iff.mpr hR
    apply ih S
    apply mul_left_cancel₀ (X_ne_zero : (X : ℂ[X]) ≠ 0)
    calc
      X * (X ^ e * B) = X ^ (e + 1) * B := by ring
      _ = (X * S) * P := hdiv
      _ = X * (S * P) := by ring

/-- The residual polynomial is normalized when both the numerator product and
the certified denominator are normalized. -/
theorem normalizedQuotient_of_laurentDivisibility {P B R : ℂ[X]} {e : ℕ}
    (hP : P.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hdiv : X ^ e * B = R * P) :
    ∃ D : ℂ[X], D.coeff 0 = 1 ∧ B = D * P := by
  obtain ⟨D, hD⟩ := quotient_of_laurentDivisibility hP e R hdiv
  refine ⟨D, ?_, hD⟩
  have hc := congrArg (fun A : ℂ[X] => A.coeff 0) hD
  simpa only [mul_coeff_zero, hB, hP, mul_one] using hc.symm

/-- Choose the normalized residual from a Laurent divisibility relation. -/
def NormalizedPolynomialQuotient.of_laurentDivisibility
    {P B R : ℂ[X]} {e : ℕ}
    (hP : P.coeff 0 = 1) (hB : B.coeff 0 = 1)
    (hdiv : X ^ e * B = R * P) : NormalizedPolynomialQuotient P B where
  polynomial := Classical.choose
    (normalizedQuotient_of_laurentDivisibility hP hB hdiv)
  coeff_zero := (Classical.choose_spec
    (normalizedQuotient_of_laurentDivisibility hP hB hdiv)).1
  factorization := (Classical.choose_spec
    (normalizedQuotient_of_laurentDivisibility hP hB hdiv)).2

/-- A zero-free product has a zero-free polynomial quotient. -/
theorem quotient_poleFree {P B D : ℂ[X]} (hD : B = D * P)
    (hB : ∀ z : ℂ, ‖z‖ < 1 → B.eval z ≠ 0) :
    ∀ z : ℂ, ‖z‖ < 1 → D.eval z ≠ 0 := by
  intro z hz hzero
  apply hB z hz
  rw [hD, eval_mul, hzero, zero_mul]

/-- The canonical reciprocal residue scale has norm strictly less than one. -/
theorem norm_residueReflection_lt_one {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) :
    ‖(LocalFactor.residueReflection F : ℂ)‖ < 1 := by
  rw [LocalFactor.coe_residueReflection, norm_inv, Complex.norm_natCast]
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  exact (inv_lt_one₀ (lt_trans zero_lt_one hq)).mpr hq

/-- Cancel the original and dual factors from a rational quotient identity.
The Laurent monomial is the explicit remaining epsilon ratio. -/
theorem reflected_identity_of_quotient_ratio {P Pdual B Bdual D E : ℂ[X]}
    (δ c : ℂˣ) (m : ℤ) (hP : P ≠ 0) (hPdual : Pdual ≠ 0)
    (hBdual : Bdual ≠ 0) (hD : B = D * P) (hE : Bdual = E * Pdual)
    (hratio : algebraMap ℂ[X] (RatFunc ℂ) B /
        LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Bdual) =
      (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
        algebraMap ℂ[X] (RatFunc ℂ) P /
          LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Pdual)) :
    algebraMap ℂ[X] (RatFunc ℂ) D =
      (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
        LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) E) := by
  have hmap (A : ℂ[X]) (hA : A ≠ 0) :
      algebraMap ℂ[X] (RatFunc ℂ) A ≠ 0 := by
    exact fun h => hA (RatFunc.algebraMap_injective ℂ (by simpa using h))
  have hreflection (A : ℂ[X]) (hA : A ≠ 0) :
      LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) A) ≠ 0 :=
    (map_ne_zero (LocalFactor.RationalReflection.subst δ)).mpr (hmap A hA)
  have hcross := (div_eq_div_iff (hreflection Bdual hBdual)
    (hreflection Pdual hPdual)).mp hratio
  rw [hD, hE, map_mul, map_mul, map_mul] at hcross
  apply mul_right_cancel₀ (hmap P hP)
  apply mul_right_cancel₀ (hreflection Pdual hPdual)
  calc
    _ = _ := hcross
    _ = _ := by ring

/-- Once the reflected residual identity is supplied, zero-freeness of the
original and dual products removes both normalized residual quotients. -/
theorem eq_of_reflected_quotients {P Pdual B Bdual D E : ℂ[X]}
    (δ c : ℂˣ) (m : ℤ) (hδ : ‖(δ : ℂ)‖ < 1)
    (hD0 : D.coeff 0 = 1) (hE0 : E.coeff 0 = 1)
    (hD : B = D * P) (hE : Bdual = E * Pdual)
    (hB : ∀ z : ℂ, ‖z‖ < 1 → B.eval z ≠ 0)
    (hBdual : ∀ z : ℂ, ‖z‖ < 1 → Bdual.eval z ≠ 0)
    (hidentity : algebraMap ℂ[X] (RatFunc ℂ) D =
      (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
        LocalFactor.RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) E)) :
    P = B ∧ Pdual = Bdual ∧ (∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0) := by
  obtain ⟨hDone, hEone⟩ := reflectionRigidity 1 1 δ c m D E
    zero_lt_one zero_lt_one (by simpa using hδ) hD0 hE0
    (quotient_poleFree hD hB) (quotient_poleFree hE hBdual) hidentity
  have hPB : P = B := by simpa [hDone] using hD.symm
  have hPdual : Pdual = Bdual := by simpa [hEone] using hE.symm
  exact ⟨hPB, hPdual, by simpa [hPB] using hB⟩

/-- Normalization and divisibility compose across the two block families. -/
theorem normalizedQuotient_doubleProduct {k l : ℕ}
    {P : ℂ[X]} {A : Fin k → ℂ[X]} {Q : Fin k → Fin l → ℂ[X]}
    (hP : P.coeff 0 = 1) (hA : ∀ i, (A i).coeff 0 = 1)
    (hQ : ∀ i j, (Q i j).coeff 0 = 1)
    (houter : ∃ (R : ℂ[X]) (e : ℕ), X ^ e * ∏ i, A i = R * P)
    (hinner : ∀ i, ∃ (R : ℂ[X]) (e : ℕ), X ^ e * ∏ j, Q i j = R * A i) :
    ∃ D : ℂ[X], D.coeff 0 = 1 ∧ (∏ i, ∏ j, Q i j) = D * P := by
  classical
  have hAnorm : (∏ i, A i).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    simp only [← coeff_zero_eq_eval_zero, hA, Finset.prod_const_one]
  obtain ⟨R, e, hR⟩ := houter
  obtain ⟨D, hDnorm, hD⟩ := normalizedQuotient_of_laurentDivisibility hP hAnorm hR
  have hrows : ∀ i, ∃ E : ℂ[X], E.coeff 0 = 1 ∧ (∏ j, Q i j) = E * A i := by
    intro i
    obtain ⟨S, f, hS⟩ := hinner i
    have hrow : (∏ j, Q i j).coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero, eval_prod]
      simp only [← coeff_zero_eq_eval_zero, hQ, Finset.prod_const_one]
    exact normalizedQuotient_of_laurentDivisibility (hA i) hrow hS
  choose E hEnorm hE using hrows
  refine ⟨(∏ i, E i) * D, ?_, ?_⟩
  · rw [mul_coeff_zero, hDnorm, mul_one, coeff_zero_eq_eval_zero, eval_prod]
    simp only [← coeff_zero_eq_eval_zero, hEnorm, Finset.prod_const_one]
  · simp only [hE, Finset.prod_mul_distrib]
    rw [hD, mul_assoc]

/-- Package the residual produced by divisibility across two block families. -/
def NormalizedPolynomialQuotient.of_doubleProduct {k l : ℕ}
    {P : ℂ[X]} {A : Fin k → ℂ[X]} {Q : Fin k → Fin l → ℂ[X]}
    (hP : P.coeff 0 = 1) (hA : ∀ i, (A i).coeff 0 = 1)
    (hQ : ∀ i j, (Q i j).coeff 0 = 1)
    (houter : ∃ (R : ℂ[X]) (e : ℕ), X ^ e * ∏ i, A i = R * P)
    (hinner : ∀ i, ∃ (R : ℂ[X]) (e : ℕ), X ^ e * ∏ j, Q i j = R * A i) :
    NormalizedPolynomialQuotient P (∏ i, ∏ j, Q i j) where
  polynomial := Classical.choose
    (normalizedQuotient_doubleProduct hP hA hQ houter hinner)
  coeff_zero := (Classical.choose_spec
    (normalizedQuotient_doubleProduct hP hA hQ houter hinner)).1
  factorization := (Classical.choose_spec
    (normalizedQuotient_doubleProduct hP hA hQ houter hinner)).2

/-- Uniqueness transfers the existential block pole bound to any certified
polynomial of that pair. The analytic theorem is an explicit input here. -/
theorem certifiedSquareIntegrable_poleFree
    (hPole : SquareIntegrablePoleFreeStatement.{uF, uV, uW})
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
    {r t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hπ : Representation.IsIrreducible π)
    (hπsq : F.canonicalTopologicalData.IsSquareIntegrable π)
    (hσ : Representation.IsIrreducible σ)
    (hσsq : F.canonicalTopologicalData.IsSquareIntegrable σ)
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P) :
    ∀ z : ℂ, ‖z‖ < 1 → P.eval z ≠ 0 := by
  obtain ⟨Q, hQ, hQpole⟩ := hPole p F ψ ν r t π σ hπ hπsq hσ hσsq
  rwa [hP.unique hQ]

end TemperedLFactorAlgebra

end Langlands.RankinSelberg
