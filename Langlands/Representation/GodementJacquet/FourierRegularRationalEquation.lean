import Langlands.Representation.GodementJacquet.SupercuspidalFourierRegularEquation
import Langlands.Representation.GodementJacquet.ContinuedMatrixCovariance
import Langlands.Representation.RankinSelberg.RationalMonomialFunctionalEquation
import Langlands.Representation.RankinSelberg.SpectralRescaling

/-! # Shifted rational equations on Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg LocalFactor

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fourierRegularRationalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fourierRegularRationalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance fourierRegularRationalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance fourierRegularRationalT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance fourierRegularRationalDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance fourierRegularRationalMeasurable : MeasurableSpace F.Carrier := borel _
local instance fourierRegularRationalBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance fourierRegularRationalGLMeasurable (m : ℕ) :
    MeasurableSpace (GeneralLinear (m + 1) F.Carrier) := borel _
local instance fourierRegularRationalGLBorel (m : ℕ) :
    BorelSpace (GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abvF" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "μF" => generalLinearHaar F.Carrier n

/-- The fixed scalar introduced by writing an unshifted monomial in the
normalized spectral parameter. -/
def shiftedMatrixMonomialUnit (n : ℕ) (c : ℂˣ) (k : ℤ) : ℂˣ :=
  c * spectralShiftUnit qF F.canonicalTopologicalData.residueCardinality_gt_one
    (jpssShift n) ^ k

theorem epsilonMonomial_shiftedMatrixMonomialUnit
    (c : ℂˣ) (k : ℤ) (s : ℂ) :
    epsilonMonomial qF (shiftedMatrixMonomialUnit F n c k) k s =
      (c : ℂ) * spectralPoint qF (s + jpssShift n) ^ k := by
  simp only [epsilonMonomial, shiftedMatrixMonomialUnit, Units.val_mul,
    Units.val_zpow_eq_zpow_val, coe_spectralShiftUnit,
    spectralPoint_add F.canonicalTopologicalData.residueCardinality_gt_one, mul_zpow]
  ring

/-- For a regular test and a continuous coefficient, every supplied actual
rational value agrees with the convergent integral at every parameter. -/
theorem regularMatrixRationalValue_eval
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (f : GeneralLinear (n + 1) F.Carrier → ℂ) (hf : Continuous f)
    (R : RationalFunctions)
    (hR : HasShiftedRationalValue qF abvF μF Φ.val f R) (s : ℂ) :
    R.denom.eval (spectralPoint qF s) ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) (spectralPoint qF s) R =
        matrixIntegral F Φ.val (s + jpssShift n) f := by
  obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_of_hasCompactSupport F Φ.val f hf
    (hasCompactSupport_restrict_of_mem_regularMatrixTests (n + 1) Φ.property).mul_right
  have hAR : HasRationalContinuation qF
      (fun s => matrixIntegral F Φ.val (s + jpssShift n) f) (laurentToRatFunc A) := by
    refine ⟨0, fun s _ => ?_⟩
    obtain ⟨hd, he⟩ := laurentToRatFunc_regular_and_eval
      (spectralUnit (Nat.zero_lt_one.trans
        F.canonicalTopologicalData.residueCardinality_gt_one) s) A
    exact ⟨hd, (hA s).2.trans he.symm⟩
  have heq := hAR.unique F.canonicalTopologicalData.residueCardinality_gt_one hR.2
  rw [← heq]
  obtain ⟨hd, he⟩ := laurentToRatFunc_regular_and_eval
    (spectralUnit (Nat.zero_lt_one.trans
      F.canonicalTopologicalData.residueCardinality_gt_one) s) A
  exact ⟨hd, he.trans (hA s).2.symm⟩

/-- An all-parameter unshifted operator equation gives the normalized
functional equation for every supplied pair of actual rational values. -/
theorem normalizedFunctionalEquation_of_fourierRegular_operator
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd)
    (hFE : ∀ s : ℂ,
      fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ)
    (v : V) (ℓ : Module.Dual ℂ V) (R RDual : RationalFunctions)
    (hR : HasShiftedRationalValue qF abvF μF Φ.val (matrixCoefficient ρ ℓ v) R)
    (hD : HasShiftedRationalValue qF abvF μF
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val)
      (coefficientIota (matrixCoefficient ρ ℓ v)) RDual) :
    NormalizedFunctionalEquation qF 1 1 1
      (shiftedMatrixMonomialUnit F n c k) 0 k R RDual := by
  have hf : Continuous (matrixCoefficient ρ ℓ v) :=
    ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp ℓ).continuous
  have hfι : Continuous (coefficientIota (matrixCoefficient ρ ℓ v)) :=
    hf.comp (GeneralLinear.continuous_inverseTranspose _ _)
  intro s _ _
  have hRe := (regularMatrixRationalValue_eval F ⟨Φ.val, Φ.property.1⟩
    (matrixCoefficient ρ ℓ v) hf R hR s).2
  have hDe := (regularMatrixRationalValue_eval F
    ⟨rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ.val, Φ.property.2⟩
    (coefficientIota (matrixCoefficient ρ ℓ v)) hfι RDual hD (1 - s)).2
  simp only [Polynomial.eval_one, Units.val_one, one_pow, one_mul]
  rw [hRe, hDe, epsilonMonomial_shiftedMatrixMonomialUnit]
  have hshift : ((n + 1 : ℕ) : ℂ) - (s + jpssShift n) =
      (1 - s) + jpssShift n := by
    simp only [Nat.cast_add, Nat.cast_one, jpssShift]
    ring
  have he := matrixIntegral_eq_of_fourierRegular_inverseTranspose F ρ hρ hι ψ ν hsd
    (s + jpssShift n) ((c : ℂ) * spectralPoint qF (s + jpssShift n) ^ k)
    Φ (hFE _) v ℓ
  rw [hshift] at he
  exact he

/-- The actual chosen pairings obey the reflected rational identity on the
Fourier-regular subspace, with the same globally fixed shifted monomial. -/
theorem matrixRationalPairing_identity_of_fourierRegular_operator
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hIotaRat : ∀ (Φ : MatrixTestFunction n F.Carrier) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd)
    (hFE : ∀ s : ℂ,
      fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ)
    (v : V) :
    RationalReflection.subst
        (spectralReflectionUnit (Nat.zero_lt_one.trans
          F.canonicalTopologicalData.residueCardinality_gt_one))
        (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hIotaRat Φ.val v) =
      laurentToRatFunc (laurentMonomialUnit (shiftedMatrixMonomialUnit F n c k) k :
        LaurentCoefficients) * matrixCoefficientRationalPairing F ρ ℓ hRat Φ.val v := by
  apply NormalizedFunctionalEquation.rational_identity
    F.canonicalTopologicalData.residueCardinality_gt_one
  exact normalizedFunctionalEquation_of_fourierRegular_operator F ρ hρ hι
    ψ ν hsd c k Φ hFE v ℓ _ _
    (matrixCoefficientRationalPairing_spec F ρ ℓ hRat Φ.val v)
    (iotaFourierMatrixCoefficientRationalPairing_spec F ψ ν hsd ρ ℓ hIotaRat Φ.val v)

end Langlands.GodementJacquet.Padic
