import Langlands.Representation.Conductor.SchurPolynomialSupport
import Langlands.Representation.Conductor.SphericalSeparation

/-! # Integral last-row support from polynomial degree coefficients -/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa
open Langlands.GeneralLinear.Spherical

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable (w : (coefficientModel π ℓ).toSubmodule)

/-- Every Laurent degree coefficient comes from an ordinary multivariate polynomial. -/
def HasPolynomialCorankOneDegreeCoefficients : Prop :=
  ∀ d, ∃ p : MvPolynomial (Fin (n + 1)) ℂ,
    algebraMap (MvPolynomial (Fin (n + 1)) ℂ)
      (TorusPolynomialAlgebra (Fin (n + 1)) ℂ) p =
        (degreeCorankOneModelCoefficient h π hπ ℓ w d).val

/-- Polynomial degree coefficients force vanishing at dominant torus points with
negative last exponent. -/
theorem torus_eq_zero_of_negative_last_of_polynomial_degreeCoefficients
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hpoly : HasPolynomialCorankOneDegreeCoefficients h π hπ ℓ w)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam)
    (hneg : lam (Fin.last n) < 0) :
    w.val.val (rankInclusion 1 (torus ϖ lam)) = 0 := by
  classical
  obtain ⟨b, hb⟩ := model_corankOne_polynomial_exponents_lower_bound h.uniformizer π hπ ψ ℓ
    abv q h.conductor w
  by_contra hW
  set d : ℤ := ∑ i, lam i
  set S := (boundedDegreeExponents_finite n b d).toFinset
  let c : {lam : Fin (n + 1) → ℤ // Antitone lam} → ℂ := fun ν =>
    ((μ.real (sphericalCell h.uniformizer ν.val) : ℝ) : ℂ) *
      (w.val.val (rankInclusion 1 (torus ϖ ν.val)) *
        determinantWeight abv (torus ϖ ν.val) (0 - 1 / 2) * halfModulus q ν.val)
  let f : (Fin (n + 1) → ℤ) → symmetricTorusSubalgebra (Fin (n + 1)) ℂ := fun lam' =>
    if Antitone lam' then
      (((μ.real (sphericalCell h.uniformizer lam') : ℝ) : ℂ) *
        (w.val.val (rankInclusion 1 (torus ϖ lam')) *
          determinantWeight abv (torus ϖ lam') (0 - 1 / 2) * halfModulus q lam')) •
        symmetricTorusSchur ℂ lam'
    else 0
  have hsum : ∑ ν ∈ S.subtype Antitone, c ν • symmetricTorusSchur ℂ ν.val =
      degreeCorankOneModelCoefficient h π hπ ℓ w d := by
    have h1 : ∑ ν ∈ S.subtype Antitone, c ν • symmetricTorusSchur ℂ ν.val =
        ∑ ν ∈ S.subtype Antitone, f ν.val := by
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      dsimp only [f, c]
      rw [ite_eq_left ν.property]
    have h2 : ∑ lam' ∈ S, f lam' = degreeCorankOneModelCoefficient h π hπ ℓ w d := by
      rw [degreeCorankOneModelCoefficient_eq_sum h π hπ ℓ w hw b hb d]
      refine Finset.sum_congr rfl (fun lam' _ => ?_)
      dsimp only [f]
      by_cases ha : Antitone lam'
      · rw [ite_eq_left ha, cellCorankOneValue_of_antitone h π ℓ w ha, smul_smul]
      · rw [ite_eq_right ha, cellCorankOneValue_of_not_antitone h π ℓ w ha, smul_zero]
    have h3 : ∀ lam' ∈ S, f lam' ≠ 0 → Antitone lam' := by
      intro lam' _ hf
      by_contra ha
      apply hf
      dsimp only [f]
      rw [ite_eq_right ha]
    rw [h1, Finset.sum_subtype_eq_sum_filter, Finset.sum_filter_of_ne h3, h2]
  have hcoef : w.val.val (rankInclusion 1 (torus ϖ lam)) *
      determinantWeight abv (torus ϖ lam) (0 - 1 / 2) * halfModulus q lam ≠ 0 :=
    mul_ne_zero (mul_ne_zero hW (determinantWeight_ne_zero abv _ _)) (halfModulus_ne_zero h lam)
  have hmem : (⟨lam, hlam⟩ : {lam : Fin (n + 1) → ℤ // Antitone lam}) ∈
      S.subtype Antitone := by
    rw [Finset.mem_subtype]
    refine (Set.Finite.mem_toFinset _).mpr ⟨fun i => ?_, rfl⟩
    have hne : corankOnePolynomialFunction ψ abv h.uniformizer q w.val (torus ϖ lam) ≠ 0 := by
      change cellCorankOneValue h π ℓ w lam ≠ 0
      rw [cellCorankOneValue_of_antitone h π ℓ w hlam]
      intro hz
      apply (symmetricTorusSchur_linearIndependent ℂ n).ne_zero ⟨lam, hlam⟩
      have := congrArg (fun z => (w.val.val (rankInclusion 1 (torus ϖ lam)) *
        determinantWeight abv (torus ϖ lam) (0 - 1 / 2) * halfModulus q lam)⁻¹ • z) hz
      simpa only [smul_smul, inv_mul_cancel₀ hcoef, one_smul, smul_zero] using this
    have := hb (torus ϖ lam) hne i
    rwa [exponent_torus] at this
  have hpolySchur : HasPolynomialTorusSchurExpansion ℂ (S.subtype Antitone) c := by
    obtain ⟨p, hp⟩ := hpoly d
    refine ⟨p, ?_⟩
    have hs := congrArg (symmetricTorusSubalgebra (Fin (n + 1)) ℂ).val hsum
    simpa only [map_sum, map_smul, Subalgebra.val_apply, symmetricTorusSchur] using hs.trans hp.symm
  have hc := hpolySchur.coefficient_eq_zero ℂ ⟨lam, hlam⟩ hmem hneg
  have hmass : (0 : ℝ) < μ.real (sphericalCell h.uniformizer lam) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (sphericalCell_measure h lam).1.ne'
      (sphericalCell_measure h lam).2.ne
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hmass.ne') hcoef hc

/-- Polynomial degree coefficients imply integral last-row support of the restriction. -/
theorem integral_last_row_of_polynomial_degreeCoefficients
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hpoly : HasPolynomialCorankOneDegreeCoefficients h π hπ ℓ w)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hW : w.val.val (rankInclusion 1 g) ≠ 0)
    (j : Fin (n + 1)) :
    g.val (Fin.last n) j ∈ (ValuativeRel.valuation F).integer := by
  classical
  obtain ⟨u, hu, k, hk, heq⟩ := exists_eq_exponent h.uniformizer g
  have heq' : g = (⟨u, hu⟩ : upperUnipotent (n + 1) F).val *
      torus ϖ (exponent h.uniformizer g) * k := heq
  have htorus : w.val.val
      (rankInclusion 1 (torus ϖ (exponent h.uniformizer g))) ≠ 0 := by
    intro hz
    apply hW
    rw [heq', hw _ ⟨k, hk⟩, map_mul]
    change w.val.val ((corankOneUnipotent ⟨u, hu⟩).val *
      rankInclusion 1 (torus ϖ (exponent h.uniformizer g))) = 0
    rw [w.val.property, hz, mul_zero]
  have hnonneg : 0 ≤ exponent h.uniformizer g (Fin.last n) := by
    by_contra hn
    have hneg : exponent h.uniformizer g (Fin.last n) < 0 := lt_of_not_ge hn
    apply htorus
    by_cases ha : Antitone (exponent h.uniformizer g)
    · exact torus_eq_zero_of_negative_last_of_polynomial_degreeCoefficients
        h π hπ ℓ w hw hpoly ha hneg
    · exact torus_eq_zero_of_not_antitone_of_restriction h π ℓ w hw ha
  have hrow : g.val (Fin.last n) j =
      ((ϖ ^ exponent h.uniformizer g (Fin.last n) : Fˣ) : F) *
        k.val (Fin.last n) j := by
    conv_lhs => rw [heq']
    change ((u.val * (torus ϖ (exponent h.uniformizer g)).val) * k.val)
      (Fin.last n) j = _
    rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_eq_single (Fin.last n)]
    · rw [hu.2 (Fin.last n), one_mul, torus_val, Matrix.diagonal_mul]
    · intro a ha
      have hz : u.val (Fin.last n) a = 0 :=
        hu.1 (lt_of_le_of_ne (Fin.le_last a) ha)
      exact mul_eq_zero_of_left hz _
  rw [hrow]
  exact (ValuativeRel.valuation F).integer.mul_mem
    ((uniformizer_zpow_mem_integer_iff h.uniformizer _).mpr hnonneg)
    (((mem_integralSubgroup (ValuativeRel.valuation F).integer n k).mp hk).1 _ _)

end Langlands.Conductor
