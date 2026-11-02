import Langlands.Global.Factors.SeparationStatement
import Langlands.Representation.RankinSelberg.RationalEvaluation

noncomputable section

namespace Langlands.Global

open Polynomial LocalFactor
open RankinSelberg.RationalEvaluation

private theorem polynomial_ne_zero {P : ℂ[X]} (hP : P.eval 0 ≠ 0) : P ≠ 0 := by
  intro h
  exact hP (by simp [h])

/-- Root-factor induction retains multiplicities when all other factors are regular. -/
private theorem dvd_of_regular_cross (P Q : ℂ[X]) (R S : RatFunc ℂ)
    (hP0 : P.eval 0 ≠ 0)
    (hR : ∀ z : ℂ, z ≠ 0 → RegularAt R z)
    (hS : ∀ z : ℂ, z ≠ 0 → RegularAt S z)
    (hsep : ∀ z : ℂ, z ≠ 0 → P.eval z = 0 →
      RatFunc.eval (RingHom.id ℂ) z S ≠ 0)
    (hid : algebraMap ℂ[X] (RatFunc ℂ) P * R =
      algebraMap ℂ[X] (RatFunc ℂ) Q * S) : P ∣ Q := by
  classical
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P Q with
  | h n ih =>
    by_cases hd : P.natDegree = 0
    · have hc : P.coeff 0 ≠ 0 := by simpa only [coeff_zero_eq_eval_zero] using hP0
      rw [eq_C_of_natDegree_eq_zero hd]
      exact (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).dvd
    obtain ⟨z, hPz⟩ := Complex.exists_root
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd))
    have hz : z ≠ 0 := by
      intro hz
      subst z
      exact hP0 hPz
    have hQz : Q.eval z = 0 := by
      have he := congrArg (RatFunc.eval (RingHom.id ℂ) z) hid
      rw [RankinSelberg.RationalEvaluation.eval_mul (RegularAt.polynomial P) (hR z hz),
        RankinSelberg.RationalEvaluation.eval_mul (RegularAt.polynomial Q) (hS z hz)] at he
      have he' : P.eval z * RatFunc.eval (RingHom.id ℂ) z R =
          Q.eval z * RatFunc.eval (RingHom.id ℂ) z S := by simpa using he
      rw [hPz, zero_mul] at he'
      exact (mul_eq_zero.mp he'.symm).resolve_right (hsep z hz hPz)
    obtain ⟨P₁, hP₁⟩ := dvd_iff_isRoot.mpr hPz
    obtain ⟨Q₁, hQ₁⟩ := dvd_iff_isRoot.mpr hQz
    have hP₁0 : P₁.eval 0 ≠ 0 := by
      intro hzero
      apply hP0
      rw [hP₁, Polynomial.eval_mul, hzero, mul_zero]
    have hdeg : P₁.natDegree < n := by
      rw [← hn, hP₁, natDegree_mul (X_sub_C_ne_zero z) (polynomial_ne_zero hP₁0),
        natDegree_X_sub_C]
      omega
    have hsep₁ : ∀ w : ℂ, w ≠ 0 → P₁.eval w = 0 →
        RatFunc.eval (RingHom.id ℂ) w S ≠ 0 := by
      intro w hw hroot
      apply hsep w hw
      rw [hP₁, Polynomial.eval_mul, hroot, mul_zero]
    have hid₁ : algebraMap ℂ[X] (RatFunc ℂ) P₁ * R =
        algebraMap ℂ[X] (RatFunc ℂ) Q₁ * S := by
      apply mul_left_cancel₀ (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero z))
      calc
        _ = algebraMap ℂ[X] (RatFunc ℂ) P * R := by rw [hP₁, map_mul, mul_assoc]
        _ = algebraMap ℂ[X] (RatFunc ℂ) Q * S := hid
        _ = _ := by rw [hQ₁, map_mul, mul_assoc]
    have hdiv := ih P₁.natDegree hdeg P₁ Q₁ hP₁0 hsep₁ hid₁ rfl
    rw [hP₁, hQ₁]
    exact mul_dvd_mul_left _ hdiv

private theorem eq_of_normalized_dvd_dvd (P Q : ℂ[X])
    (hP : P.eval 0 = 1) (hQ : Q.eval 0 = 1) (hPQ : P ∣ Q) (hQP : Q ∣ P) : P = Q := by
  have hPne : P ≠ 0 := polynomial_ne_zero (by rw [hP]; exact one_ne_zero)
  have hQne : Q ≠ 0 := polynomial_ne_zero (by rw [hQ]; exact one_ne_zero)
  obtain ⟨A, hA⟩ := hPQ
  have hAne : A ≠ 0 := by intro h; simp [h] at hA; exact hQne hA
  have hdeg : A.natDegree = 0 := by
    have hle := natDegree_le_of_dvd hQP hPne
    rw [hA, natDegree_mul hPne hAne] at hle
    omega
  have hA0 : A.eval 0 = 1 := by
    have he := congrArg (fun B : ℂ[X] => B.eval 0) hA
    simpa only [Polynomial.eval_mul, hP, hQ, one_mul] using he.symm
  have hAone : A = 1 := by
    rw [eq_C_of_natDegree_eq_zero hdeg, coeff_zero_eq_eval_zero, hA0, C_1]
  simpa only [hAone, mul_one] using hA.symm

private theorem monomial_regular_nonzero (a : ℂˣ) (m : ℤ) (z : ℂ) (hz : z ≠ 0) :
    RegularAt (RatFunc.C (a : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) z ∧
      RatFunc.eval (RingHom.id ℂ) z
        (RatFunc.C (a : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) ≠ 0 := by
  have hc : RegularAt (RatFunc.C (a : ℂ)) z :=
    RegularAt.of_eval_ne_zero (by simp)
  have hx : RatFunc.eval (RingHom.id ℂ) z RatFunc.X ≠ 0 := by simpa using hz
  have hm := RegularAt.zpow hx m
  refine ⟨hc.mul hm, ?_⟩
  rw [RankinSelberg.RationalEvaluation.eval_mul hc hm, eval_zpow hx]
  simpa using mul_ne_zero a.ne_zero (zpow_ne_zero m hz)

/-- The four normalized polynomials and epsilon monomials are separated by their
actual nonzero zeros and poles, with multiplicities retained by divisibility. -/
theorem gammaPolynomialSeparation : GammaPolynomialSeparationStatement := by
  intro q hq P Pdual Q Qdual a c m k hP hPdual hQ hQdual hsepP hsepQ
  dsimp only
  intro hid
  have hqne : (q : ℂ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by omega)
  let δ : ℂˣ := Units.mk0 (q : ℂ)⁻¹ (inv_ne_zero hqne)
  let U : RatFunc ℂ := RatFunc.C (a : ℂ) * RatFunc.X ^ m
  let V : RatFunc ℂ := RatFunc.C (c : ℂ) * RatFunc.X ^ k
  have hU := monomial_regular_nonzero a m
  have hV := monomial_regular_nonzero c k
  have href : RationalReflection.reflectedVariable δ =
      (RatFunc.C (q : ℂ))⁻¹ * (RatFunc.X : RatFunc ℂ)⁻¹ := by
    simp only [RationalReflection.reflectedVariable, δ, Units.val_mk0,
      RatFunc.algebraMap_eq_C, map_inv₀, div_eq_mul_inv]
  have hregular (A : ℂ[X]) (z : ℂ) (hz : z ≠ 0) :
      RegularAt (RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) A)) z :=
    regular_subst δ hz (RegularAt.polynomial A)
  have heval (A : ℂ[X]) (z : ℂ) (hz : z ≠ 0) :
      RatFunc.eval (RingHom.id ℂ) z
        (RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) A)) =
          A.eval ((q : ℂ)⁻¹ * z⁻¹) := by
    rw [eval_subst δ hz (RegularAt.polynomial A)]
    simp [δ, div_eq_mul_inv]
  have hnonzero (A : ℂ[X]) (hA : A.eval 0 = 1) :
      RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) A) ≠ 0 :=
    (map_ne_zero (RationalReflection.subst δ)).mpr
      (RatFunc.algebraMap_ne_zero (polynomial_ne_zero (by rw [hA]; exact one_ne_zero)))
  have hidentity : U * algebraMap ℂ[X] (RatFunc ℂ) P /
        RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Pdual) =
      V * algebraMap ℂ[X] (RatFunc ℂ) Q /
        RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Qdual) := by
    simpa only [U, V, RationalReflection.subst_polynomial, href,
      RatFunc.aeval_X_left_eq_algebraMap] using hid
  have hcross : algebraMap ℂ[X] (RatFunc ℂ) P *
        (U * RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Qdual)) =
      algebraMap ℂ[X] (RatFunc ℂ) Q *
        (V * RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Pdual)) := by
    have h := (div_eq_div_iff (hnonzero Pdual hPdual) (hnonzero Qdual hQdual)).mp hidentity
    calc
      _ = _ := by ring
      _ = _ := h
      _ = _ := by ring
  have hUR (z : ℂ) (hz : z ≠ 0) : RegularAt
      (U * RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Qdual)) z :=
    (hU z hz).1.mul (hregular Qdual z hz)
  have hVS (z : ℂ) (hz : z ≠ 0) : RegularAt
      (V * RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Pdual)) z :=
    (hV z hz).1.mul (hregular Pdual z hz)
  have hPQ : P ∣ Q := dvd_of_regular_cross P Q _ _
    (by rw [hP]; exact one_ne_zero) hUR hVS (by
      intro z hz hroot
      rw [RankinSelberg.RationalEvaluation.eval_mul (hV z hz).1 (hregular Pdual z hz),
        heval Pdual z hz]
      exact mul_ne_zero (hV z hz).2 (fun h => hsepP z hz ⟨hroot, h⟩)) hcross
  have hQP : Q ∣ P := dvd_of_regular_cross Q P _ _
    (by rw [hQ]; exact one_ne_zero) hVS hUR (by
      intro z hz hroot
      rw [RankinSelberg.RationalEvaluation.eval_mul (hU z hz).1 (hregular Qdual z hz),
        heval Qdual z hz]
      exact mul_ne_zero (hU z hz).2 (fun h => hsepQ z hz ⟨hroot, h⟩)) hcross.symm
  have hPeq : P = Q := eq_of_normalized_dvd_dvd P Q hP hQ hPQ hQP
  have hremain : U * RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Qdual) =
      V * RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) Pdual) := by
    apply mul_left_cancel₀
      (RatFunc.algebraMap_ne_zero (polynomial_ne_zero (by rw [hP]; exact one_ne_zero)))
    simpa only [← hPeq] using hcross
  have hdual : algebraMap ℂ[X] (RatFunc ℂ) Pdual * RationalReflection.subst δ V =
      algebraMap ℂ[X] (RatFunc ℂ) Qdual * RationalReflection.subst δ U := by
    have h := congrArg (RationalReflection.subst δ) hremain
    simpa only [map_mul, RationalReflection.subst_subst, mul_comm] using h.symm
  have hsubU (z : ℂ) (hz : z ≠ 0) :
      RegularAt (RationalReflection.subst δ U) z ∧
        RatFunc.eval (RingHom.id ℂ) z (RationalReflection.subst δ U) ≠ 0 := by
    have hw := div_ne_zero δ.ne_zero hz
    refine ⟨regular_subst δ hz (hU _ hw).1, ?_⟩
    rw [eval_subst δ hz (hU _ hw).1]
    exact (hU _ hw).2
  have hsubV (z : ℂ) (hz : z ≠ 0) :
      RegularAt (RationalReflection.subst δ V) z ∧
        RatFunc.eval (RingHom.id ℂ) z (RationalReflection.subst δ V) ≠ 0 := by
    have hw := div_ne_zero δ.ne_zero hz
    refine ⟨regular_subst δ hz (hV _ hw).1, ?_⟩
    rw [eval_subst δ hz (hV _ hw).1]
    exact (hV _ hw).2
  have hPdQd : Pdual ∣ Qdual := dvd_of_regular_cross Pdual Qdual _ _
    (by rw [hPdual]; exact one_ne_zero) (fun z hz => (hsubV z hz).1)
    (fun z hz => (hsubU z hz).1) (fun z hz _ => (hsubU z hz).2) hdual
  have hQdPd : Qdual ∣ Pdual := dvd_of_regular_cross Qdual Pdual _ _
    (by rw [hQdual]; exact one_ne_zero) (fun z hz => (hsubU z hz).1)
    (fun z hz => (hsubV z hz).1) (fun z hz _ => (hsubV z hz).2) hdual.symm
  have hDeq : Pdual = Qdual :=
    eq_of_normalized_dvd_dvd Pdual Qdual hPdual hQdual hPdQd hQdPd
  refine ⟨hPeq, hDeq, ?_⟩
  change U = V
  apply mul_right_cancel₀ (hnonzero Pdual hPdual)
  simpa only [← hDeq] using hremain

/-- Reciprocal root lower bounds yield the required strict separation. -/
theorem reflectedRootRegion : ReflectedRootRegionStatement := by
  intro q hq r hr P Pdual hP hPdual z hz hroots
  have hqreal : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := lt_trans zero_lt_one hqreal
  have hqinv : (q : ℝ)⁻¹ < 1 := (inv_lt_one₀ hqpos).mpr hqreal
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hbound : r⁻¹ ≤ (q : ℝ)⁻¹ / ‖z‖ := by
    simpa only [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv] using
      hPdual _ hroots.2
  have hprod : r⁻¹ * ‖z‖ ≤ (q : ℝ)⁻¹ := (le_div_iff₀ hnorm).mp hbound
  have hone : 1 ≤ r⁻¹ * ‖z‖ := by
    calc
      1 = r⁻¹ * r := (inv_mul_cancel₀ hr.ne').symm
      _ ≤ r⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_left (hP z hroots.1) (inv_nonneg.mpr hr.le)
  exact (not_le_of_gt hqinv) (hone.trans hprod)

/-- The exact published conjunction, including both algebraic separation and
its reciprocal root-region criterion. -/
theorem gammaSeparation : GammaSeparationStatement :=
  ⟨gammaPolynomialSeparation, reflectedRootRegion⟩

end Langlands.Global
