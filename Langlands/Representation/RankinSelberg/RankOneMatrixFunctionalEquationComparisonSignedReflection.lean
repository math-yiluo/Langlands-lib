import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonReflectedHaar
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylSigns

/-! Exact character and Haar transport for the signed long Weyl representative. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure GeneralLinear Whittaker HarmonicAnalysis

universe uK uA

variable {K : Type uK} [Field K] (n : ℕ)

/-- Alternating diagonal conjugation is an involution on the actual unipotent group. -/
theorem alternatingUnipotent_involutive :
    Function.Involutive (characterChangeConj (-1 : Kˣ) n) := by
  intro u
  apply Subtype.ext
  change rankOneWeylAlternating n *
      (rankOneWeylAlternating n * u.val * (rankOneWeylAlternating n)⁻¹) *
        (rankOneWeylAlternating n)⁻¹ = u.val
  simp only [rankOneWeylAlternating_inv, mul_assoc]
  rw [← mul_assoc (rankOneWeylAlternating n) (rankOneWeylAlternating n),
    rankOneWeylAlternating_mul_self, one_mul, mul_one]

/-- The signed Weyl conjugate of inverse transpose on the actual unipotent group. -/
def signedReflectedUnipotent (u : upperUnipotent (n + 1) K) :
    upperUnipotent (n + 1) K :=
  reflectedUnipotent (characterChangeConj (-1 : Kˣ) n u)

/-- This composite has exactly the signed matrix conjugation formula. -/
theorem signedReflectedUnipotent_val (u : upperUnipotent (n + 1) K) :
    (signedReflectedUnipotent n u).val =
      rankOneSignedWeyl n * inverseTranspose (n + 1) K u.val *
        (rankOneSignedWeyl n)⁻¹ := by
  simp only [signedReflectedUnipotent, reflectedUnipotent_val,
    characterChangeConj_val, map_mul, map_inv, inverseTranspose_characterChangeElement_neg_one,
    rankOneSignedWeyl, rankOneWeylAlternating, mul_inv_rev, weylLong_inv, mul_assoc]

/-- Moving the signed Weyl factor past the reflected unipotent is an actual group equality. -/
theorem signedWeyl_inv_mul_signedReflected (u : upperUnipotent (n + 1) K) :
    (rankOneSignedWeyl n)⁻¹ * (signedReflectedUnipotent n u).val =
      inverseTranspose (n + 1) K u.val * (rankOneSignedWeyl n)⁻¹ := by
  rw [signedReflectedUnipotent_val]
  simp only [← mul_assoc, inv_mul_cancel, one_mul]

variable [TopologicalSpace K]

omit [TopologicalSpace K] in
/-- The two sign reversals preserve the first-superdiagonal sum. -/
theorem signedReflectedUnipotent_sum (u : upperUnipotent (n + 1) K) :
    (∑ i : Fin n, (signedReflectedUnipotent n u).val i.castSucc i.succ) =
      ∑ i : Fin n, u.val i.castSucc i.succ := by
  simp only [signedReflectedUnipotent, reflectedUnipotent_sum,
    characterChangeConj_adjacent, Units.val_neg, Units.val_one,
    neg_one_mul, Finset.sum_neg_distrib, neg_neg]

/-- Signed reflection retains the same standard character, for arbitrary `ψ`. -/
@[simp] theorem standardCharacter_signedReflected (ψ : UnitaryAdditiveCharacter K)
    (u : upperUnipotent (n + 1) K) :
    standardCharacter ψ n (signedReflectedUnipotent n u) = standardCharacter ψ n u := by
  apply Units.ext
  simp only [standardCharacter_apply, signedReflectedUnipotent_sum]

/-- The inverse standard character is likewise unchanged. -/
@[simp] theorem inverseStandardCharacter_signedReflected (ψ : UnitaryAdditiveCharacter K)
    (u : upperUnipotent (n + 1) K) :
    inverseStandardCharacter ψ n (signedReflectedUnipotent n u) =
      inverseStandardCharacter ψ n u := by
  change (standardCharacter ψ n (signedReflectedUnipotent n u))⁻¹ =
    (standardCharacter ψ n u)⁻¹
  rw [standardCharacter_signedReflected]

variable [IsTopologicalRing K]

/-- Alternating diagonal conjugation as a continuous group automorphism. -/
def alternatingUnipotentEquiv :
    upperUnipotent (n + 1) K ≃ₜ* upperUnipotent (n + 1) K where
  toFun := characterChangeConj (-1 : Kˣ) n
  invFun := characterChangeConj (-1 : Kˣ) n
  left_inv := alternatingUnipotent_involutive n
  right_inv := alternatingUnipotent_involutive n
  map_mul' := (characterChangeConj (-1 : Kˣ) n).map_mul
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

/-- Signed reflection as a continuous group automorphism. -/
def signedReflectedUnipotentEquiv :
    upperUnipotent (n + 1) K ≃ₜ* upperUnipotent (n + 1) K :=
  (alternatingUnipotentEquiv n).trans (reflectedUnipotentEquiv n)

@[simp] theorem signedReflectedUnipotentEquiv_apply (u : upperUnipotent (n + 1) K) :
    signedReflectedUnipotentEquiv n u = signedReflectedUnipotent n u := rfl

variable [MeasurableSpace (upperUnipotent (n + 1) K)]
  [BorelSpace (upperUnipotent (n + 1) K)]
  [LocallyCompactSpace (upperUnipotent (n + 1) K)]

/-- Alternating conjugation preserves every regular unipotent Haar exactly. -/
theorem measurePreserving_alternatingUnipotent
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ] :
    MeasurePreserving (characterChangeConj (-1 : Kˣ) n) μ μ :=
  measurePreserving_involutive_automorphism (alternatingUnipotentEquiv n)
    (alternatingUnipotent_involutive n) μ

/-- The signed substitution introduces no Haar scalar. -/
theorem measurePreserving_signedReflectedUnipotent
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ] :
    MeasurePreserving (signedReflectedUnipotent n) μ μ :=
  (measurePreserving_reflectedUnipotent n μ).comp
    (measurePreserving_alternatingUnipotent n μ)

/-- The signed substitution also preserves any full supplied product measure. -/
theorem measurePreserving_signedReflectedUnipotent_prod
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ]
    [SFinite μ] {A : Type uA} [MeasurableSpace A] (ν : Measure A) [SFinite ν] :
    MeasurePreserving
      (fun z : upperUnipotent (n + 1) K × A => (signedReflectedUnipotent n z.1, z.2))
      (μ.prod ν) (μ.prod ν) :=
  (measurePreserving_signedReflectedUnipotent n μ).prod (MeasurePreserving.id ν)

/-- Total-integral signed orbit transport, with the same inverse character and Haar. -/
theorem integral_signedInverseTransposeOrbit
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ]
    (ψ : UnitaryAdditiveCharacter K) (f : Langlands.GeneralLinear (n + 1) K → ℂ)
    (g : Langlands.GeneralLinear (n + 1) K) :
    (∫ u, (inverseStandardCharacter ψ n u : ℂ) *
      f (inverseTranspose (n + 1) K u.val * (rankOneSignedWeyl n)⁻¹ * g) ∂μ) =
    ∫ u, (inverseStandardCharacter ψ n u : ℂ) *
      f ((rankOneSignedWeyl n)⁻¹ * u.val * g) ∂μ := by
  let e := (signedReflectedUnipotentEquiv (K := K) n).toHomeomorph.toMeasurableEquiv
  have he := (measurePreserving_signedReflectedUnipotent n μ).integral_comp
    e.measurableEmbedding (fun u => (inverseStandardCharacter ψ n u : ℂ) *
      f ((rankOneSignedWeyl n)⁻¹ * u.val * g))
  change (∫ u, (inverseStandardCharacter ψ n (signedReflectedUnipotent n u) : ℂ) *
    f ((rankOneSignedWeyl n)⁻¹ * (signedReflectedUnipotent n u).val * g) ∂μ) = _ at he
  simpa only [inverseStandardCharacter_signedReflected,
    signedWeyl_inv_mul_signedReflected] using he

/-- Absolute convergence is equivalent under the same exact signed substitution. -/
theorem integrable_signedInverseTransposeOrbit_iff
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ]
    (ψ : UnitaryAdditiveCharacter K) (f : Langlands.GeneralLinear (n + 1) K → ℂ)
    (g : Langlands.GeneralLinear (n + 1) K) :
    Integrable (fun u => (inverseStandardCharacter ψ n u : ℂ) *
      f (inverseTranspose (n + 1) K u.val * (rankOneSignedWeyl n)⁻¹ * g)) μ ↔
    Integrable (fun u => (inverseStandardCharacter ψ n u : ℂ) *
      f ((rankOneSignedWeyl n)⁻¹ * u.val * g)) μ := by
  let e := (signedReflectedUnipotentEquiv (K := K) n).toHomeomorph.toMeasurableEquiv
  have he := e.measurableEmbedding.integrable_map_iff
    (μ := μ) (g := fun u => (inverseStandardCharacter ψ n u : ℂ) *
      f ((rankOneSignedWeyl n)⁻¹ * u.val * g))
  have hp : MeasurePreserving e μ μ := measurePreserving_signedReflectedUnipotent n μ
  rw [hp.map_eq] at he
  change Integrable _ μ ↔ Integrable
    (fun u => (inverseStandardCharacter ψ n (signedReflectedUnipotent n u) : ℂ) *
      f ((rankOneSignedWeyl n)⁻¹ * (signedReflectedUnipotent n u).val * g)) μ at he
  simpa only [inverseStandardCharacter_signedReflected,
    signedWeyl_inv_mul_signedReflected] using he.symm

/-- The full signed orbit product has equivalent absolute convergence. -/
theorem integrable_signedInverseTransposeOrbit_prod_iff
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ]
    [SFinite μ] {A : Type uA} [MeasurableSpace A] (ν : Measure A) [SFinite ν]
    (ψ : UnitaryAdditiveCharacter K) (f : A → Langlands.GeneralLinear (n + 1) K → ℂ)
    (g : A → Langlands.GeneralLinear (n + 1) K) :
    Integrable (fun z : upperUnipotent (n + 1) K × A =>
      (inverseStandardCharacter ψ n z.1 : ℂ) *
        f z.2 (inverseTranspose (n + 1) K z.1.val * (rankOneSignedWeyl n)⁻¹ * g z.2))
      (μ.prod ν) ↔
    Integrable (fun z : upperUnipotent (n + 1) K × A =>
      (inverseStandardCharacter ψ n z.1 : ℂ) *
        f z.2 ((rankOneSignedWeyl n)⁻¹ * z.1.val * g z.2)) (μ.prod ν) := by
  let e := (signedReflectedUnipotentEquiv (K := K) n).toHomeomorph.toMeasurableEquiv.prodCongr
    (MeasurableEquiv.refl A)
  have hp : MeasurePreserving e (μ.prod ν) (μ.prod ν) :=
    measurePreserving_signedReflectedUnipotent_prod n μ ν
  have he := e.measurableEmbedding.integrable_map_iff (μ := μ.prod ν)
    (g := fun z : upperUnipotent (n + 1) K × A =>
      (inverseStandardCharacter ψ n z.1 : ℂ) *
        f z.2 ((rankOneSignedWeyl n)⁻¹ * z.1.val * g z.2))
  rw [hp.map_eq] at he
  change Integrable _ _ ↔ Integrable (fun z : upperUnipotent (n + 1) K × A =>
    (inverseStandardCharacter ψ n (signedReflectedUnipotent n z.1) : ℂ) *
      f z.2 ((rankOneSignedWeyl n)⁻¹ * (signedReflectedUnipotent n z.1).val * g z.2)) _ at he
  simpa only [inverseStandardCharacter_signedReflected,
    signedWeyl_inv_mul_signedReflected] using he.symm

/-- Total product integrals are unchanged by the same signed substitution. -/
theorem integral_signedInverseTransposeOrbit_prod
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ]
    [SFinite μ] {A : Type uA} [MeasurableSpace A] (ν : Measure A) [SFinite ν]
    (ψ : UnitaryAdditiveCharacter K) (f : A → Langlands.GeneralLinear (n + 1) K → ℂ)
    (g : A → Langlands.GeneralLinear (n + 1) K) :
    (∫ z : upperUnipotent (n + 1) K × A,
      (inverseStandardCharacter ψ n z.1 : ℂ) *
        f z.2 (inverseTranspose (n + 1) K z.1.val * (rankOneSignedWeyl n)⁻¹ * g z.2)
      ∂μ.prod ν) =
    ∫ z : upperUnipotent (n + 1) K × A,
      (inverseStandardCharacter ψ n z.1 : ℂ) *
        f z.2 ((rankOneSignedWeyl n)⁻¹ * z.1.val * g z.2) ∂μ.prod ν := by
  let e := (signedReflectedUnipotentEquiv (K := K) n).toHomeomorph.toMeasurableEquiv.prodCongr
    (MeasurableEquiv.refl A)
  have hp : MeasurePreserving e (μ.prod ν) (μ.prod ν) :=
    measurePreserving_signedReflectedUnipotent_prod n μ ν
  have he := hp.integral_comp e.measurableEmbedding
    (fun z : upperUnipotent (n + 1) K × A => (inverseStandardCharacter ψ n z.1 : ℂ) *
      f z.2 ((rankOneSignedWeyl n)⁻¹ * z.1.val * g z.2))
  change (∫ z : upperUnipotent (n + 1) K × A,
    (inverseStandardCharacter ψ n (signedReflectedUnipotent n z.1) : ℂ) *
      f z.2 ((rankOneSignedWeyl n)⁻¹ * (signedReflectedUnipotent n z.1).val * g z.2)
    ∂μ.prod ν) = _ at he
  simpa only [inverseStandardCharacter_signedReflected,
    signedWeyl_inv_mul_signedReflected] using he

/-- Right Haar substitution proves the standard left character covariance of
this signed inverse-transpose orbit, for arbitrary group functions. -/
theorem integral_signedInverseTransposeOrbit_left
    (μ : Measure (upperUnipotent (n + 1) K)) [IsHaarMeasure μ] [Regular μ]
    [IsMulRightInvariant μ] (ψ : UnitaryAdditiveCharacter K)
    (f : Langlands.GeneralLinear (n + 1) K → ℂ)
    (p : upperUnipotent (n + 1) K) (g : Langlands.GeneralLinear (n + 1) K) :
    (∫ u, (inverseStandardCharacter ψ n u : ℂ) *
      f (inverseTranspose (n + 1) K u.val * (rankOneSignedWeyl n)⁻¹ * (p.val * g)) ∂μ) =
    (standardCharacter ψ n p : ℂ) * ∫ u, (inverseStandardCharacter ψ n u : ℂ) *
      f (inverseTranspose (n + 1) K u.val * (rankOneSignedWeyl n)⁻¹ * g) ∂μ := by
  rw [integral_signedInverseTransposeOrbit, integral_signedInverseTransposeOrbit]
  have he (u : upperUnipotent (n + 1) K) :
      (inverseStandardCharacter ψ n u : ℂ) * f ((rankOneSignedWeyl n)⁻¹ * u.val * (p.val * g)) =
      (standardCharacter ψ n p : ℂ) * ((inverseStandardCharacter ψ n (u * p) : ℂ) *
        f ((rankOneSignedWeyl n)⁻¹ * (u * p).val * g)) := by
    change (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * _ =
      (standardCharacter ψ n p : ℂ) *
        ((((standardCharacter ψ n (u * p))⁻¹ : ℂˣ) : ℂ) * _)
    have hc : (standardCharacter ψ n p : ℂ) *
        (((standardCharacter ψ n p)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [map_mul, mul_inv_rev, Units.val_mul, Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (standardCharacter ψ n p : ℂ)
      (((standardCharacter ψ n p)⁻¹ : ℂˣ) : ℂ), hc, one_mul]
  simp only [he, integral_const_mul]
  exact congrArg ((standardCharacter ψ n p : ℂ) * ·)
    (integral_mul_right_eq_self (fun u : upperUnipotent (n + 1) K =>
      (inverseStandardCharacter ψ n u : ℂ) * f ((rankOneSignedWeyl n)⁻¹ * u.val * g)) p)

end Langlands.RankinSelberg
