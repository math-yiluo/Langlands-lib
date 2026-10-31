import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonZeroCoefficients
import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Representation.RankinSelberg.GammaFactor

/-!
# The actual equal-rank Tate passage from matrix data

The rank-zero shift vanishes. The second model is constant, and the long Weyl
matrix at rank one is the identity. The row/matrix Schwartz identification
therefore identifies both original and dual integrals, with the supplied
Fourier measure unchanged.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section Algebra

variable {F : Type uF} [Field F] [TopologicalSpace F]

omit [TopologicalSpace F] in
/-- The unsigned long Weyl matrix is the identity in dimension one. -/
theorem weylLong_rankOne_eq_one : weylLong 1 F = 1 := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [weylLong_entry]

/-- A vector in the actual model of the trivial rank-one representation is
constant, with its value at the identity as constant. -/
theorem rankOneTrivialModel_constant (ψ : UnitaryAdditiveCharacter F)
    (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)))
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule)
    (g : Langlands.GeneralLinear 1 F) : f'.val.val g = f'.val.val 1 := by
  obtain ⟨z, rfl⟩ := modelMap_surjective _ ℓ' f'
  change ℓ'.val (rankOneCharacter (1 : Fˣ →* ℂˣ) g z) =
    ℓ'.val (rankOneCharacter (1 : Fˣ →* ℂˣ) 1 z)
  simp [rankOneCharacter, characterRepresentation, twist]

/-- Every nonzero functional on the trivial rank-one representation has the
constant-one function in its actual coefficient model. -/
theorem exists_rankOneTrivialModel_one (ψ : UnitaryAdditiveCharacter F)
    (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)))
    (hℓ' : ℓ'.val ≠ 0) :
    ∃ f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule,
      ∀ g, f'.val.val g = 1 := by
  obtain ⟨z, hz⟩ :=
    (linearForm_bijective_of_complexLine (LinearEquiv.refl ℂ ℂ) ℓ'.val hℓ').2 1
  refine ⟨modelMap _ ℓ' z, fun g => ?_⟩
  change ℓ'.val (rankOneCharacter (1 : Fˣ →* ℂˣ) g z) = 1
  simpa [rankOneCharacter, characterRepresentation, twist] using hz

/-- The trivial rank-one model has minus-one scalar one. -/
theorem rankOneTrivialModel_minusOne (ψ : UnitaryAdditiveCharacter F)
    (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ))) :
    HasModelMinusOneScalar (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ' 1 := by
  intro f' g
  simp only [Units.val_one, one_mul]
  exact (rankOneTrivialModel_constant ψ ℓ' f' _).trans
    (rankOneTrivialModel_constant ψ ℓ' f' _).symm

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
  (ℓ : glFunctionals ψ 0 σ)
  (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)))

/-- Absorbing the constant second model vector identifies the genuine original
integrand with the shifted matrix integrand; the shift is zero. -/
theorem equalRankFunction_matrixIntegrand_rankOne
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    equalRankFunction ψ abv f.val f'.val Φ s =
      GodementJacquet.matrixIntegrand abv
        (schwartzBruhatComap (oneByOneRow F) Φ) (s + GodementJacquet.jpssShift 0)
        (glModelFunction ψ 0 σ ℓ (f'.val.val 1 • f)) := by
  funext g
  simp only [equalRankFunction, GodementJacquet.matrixIntegrand,
    GodementJacquet.jpssShift, Nat.cast_zero, zero_div, add_zero,
    schwartzBruhatComap_apply, ← lastRow_eq_oneByOneRow,
    glModelFunction, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    rankOneTrivialModel_constant ψ ℓ' f' g]
  ring

variable [IsTopologicalRing F]

/-- The genuine dual integrand uses the inverse additive character and the
actual unsigned Weyl representative. In rank one it is the matrix iota
integrand with the same test and zero shift. -/
theorem dualEqualRankFunction_matrixIntegrand_rankOne
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    equalRankFunction (ψ.scale (-1)) abv (firstDualFunction ψ 0 f.val)
        (secondDualFunction ψ 0 f'.val) Φ s =
      GodementJacquet.matrixIntegrand abv
        (schwartzBruhatComap (oneByOneRow F) Φ) (s + GodementJacquet.jpssShift 0)
        (GodementJacquet.coefficientIota (glModelFunction ψ 0 σ ℓ (f'.val.val 1 • f))) := by
  have hw : weylLong (0 + 1) F = 1 := weylLong_rankOne_eq_one
  funext g
  simp only [equalRankFunction, firstDualFunction_apply, secondDualFunction_apply,
    hw, one_mul, GodementJacquet.matrixIntegrand,
    GodementJacquet.coefficientIota, GodementJacquet.jpssShift,
    Nat.cast_zero, zero_div, add_zero, schwartzBruhatComap_apply,
    ← lastRow_eq_oneByOneRow, glModelFunction, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, rankOneTrivialModel_constant ψ ℓ' f']
  ring

end Algebra

section Integrals

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  [MeasurableSpace (Langlands.GeneralLinear (0 + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (0 + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [BorelSpace (LeftUnipotentQuotient 0 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
  (ℓ : glFunctionals ψ 0 σ)
  (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)))

/-- The original rank-one model integral equals the actual shifted matrix
integral, for the normalized rank-one quotient measure. -/
theorem equalRankModelIntegral_rankOne_eq_matrixIntegral
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F)
        σ (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ ℓ' f f' Φ s =
      GodementJacquet.matrixIntegral abv (generalLinearHaar F 0)
        (schwartzBruhatComap (oneByOneRow F) Φ) (s + GodementJacquet.jpssShift 0)
        (glModelFunction ψ 0 σ ℓ (f'.val.val 1 • f)) := by
  unfold equalRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar,
    equalRankFunction_matrixIntegrand_rankOne]
  rfl

/-- The actual dual rank-one model integral equals the inverse-transpose
matrix integral, with the same normalized group measure and zero shift. -/
theorem dualEqualRankModelIntegral_rankOne_eq_matrixIntegral
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    dualEqualRankModelIntegral ψ abv (rankOneQuotientHaar F)
        σ (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ ℓ' f f' Φ s =
      GodementJacquet.matrixIntegral abv (generalLinearHaar F 0)
        (schwartzBruhatComap (oneByOneRow F) Φ) (s + GodementJacquet.jpssShift 0)
        (GodementJacquet.coefficientIota
          (glModelFunction ψ 0 σ ℓ (f'.val.val 1 • f))) := by
  unfold dualEqualRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar,
    dualEqualRankFunction_matrixIntegrand_rankOne]
  rfl

/-- Absolute convergence of the original integral is exactly the corresponding
matrix convergence, before any rational continuation is used. -/
theorem equalRankConverges_rankOne_iff_matrixConverges
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    EqualRankConverges ψ abv (rankOneQuotientHaar F) f.val f'.val Φ s ↔
      GodementJacquet.MatrixConverges abv (generalLinearHaar F 0)
        (schwartzBruhatComap (oneByOneRow F) Φ) (s + GodementJacquet.jpssShift 0)
        (glModelFunction ψ 0 σ ℓ (f'.val.val 1 • f)) := by
  rw [equalRankConverges_rankOneQuotientHaar_iff,
    equalRankFunction_matrixIntegrand_rankOne]
  rfl

/-- The same absolute-convergence comparison holds for the genuine dual
functions with their inverse character and unsigned Weyl matrix. -/
theorem dualEqualRankConverges_rankOne_iff_matrixConverges
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    EqualRankConverges (ψ.scale (-1)) abv (rankOneQuotientHaar F)
        (firstDualFunction ψ 0 f.val) (secondDualFunction ψ 0 f'.val) Φ s ↔
      GodementJacquet.MatrixConverges abv (generalLinearHaar F 0)
        (schwartzBruhatComap (oneByOneRow F) Φ) (s + GodementJacquet.jpssShift 0)
        (GodementJacquet.coefficientIota
          (glModelFunction ψ 0 σ ℓ (f'.val.val 1 • f))) := by
  rw [equalRankConverges_rankOneQuotientHaar_iff,
    dualEqualRankFunction_matrixIntegrand_rankOne]
  rfl

end Integrals

section Equation

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [MeasurableSpace (Langlands.GeneralLinear (0 + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (0 + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [BorelSpace (LeftUnipotentQuotient 0 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
  (hσ : IsOfWhittakerType 0 (standardCharacter ψ 0) σ)
  (ℓ : glFunctionals ψ 0 σ) (hℓ : ℓ.val ≠ 0)
  (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)))
  (hℓ' : ℓ'.val ≠ 0)

/-- Absorb the constant second vector into the first and regard its underlying
function as an actual bi-smooth coefficient of the model representation. -/
def rankOneModelMatrixCoefficient
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule) :
    GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule)
      (glModelRepresentation ψ 0 σ ℓ) :=
  ⟨glModelFunction ψ 0 σ ℓ (f'.val.val 1 • f),
    glModelFunction_mem_biSmooth_rankOne ψ σ hσ ℓ hℓ _⟩

include hσ hℓ hℓ'

/-- Actual normalized matrix data imply the fixed-functional equal-rank
gamma equation in rank one, on the full reduced-denominator domain. -/
theorem equalRankGammaEquation_rankOne_of_matrix
    {q : ℕ} (hq : 1 < q) (ν : AdditiveHaarMeasure F)
    {P PDual : Polynomial ℂ} {c δ : ℂˣ} {a : ℤ}
    (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hdata : GodementJacquet.NormalizedMatrixFunctionalEquationData q ψ ν abv
      (generalLinearHaar F 0)
      (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule)
      (glModelRepresentation ψ 0 σ ℓ) P PDual c a) :
    EqualRankGammaEquation q ψ abv (rankOneQuotientHaar F) ν
      σ (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ ℓ'
      (rationalGammaExpression δ c a P PDual) := by
  refine ⟨1, rankOneTrivialModel_minusOne ψ ℓ', ?_, ?_⟩
  · obtain ⟨R, ⟨Φmat, fc, hR⟩, hR0⟩ := hdata.1.2.2.exists_ne_zero
    have hfc : fc.val ∈ (glModelFunctionLinearMap ψ σ ℓ).range :=
      (biSmoothMatrixCoefficients_rankOne_model ψ σ hσ ℓ hℓ).le fc.property
    obtain ⟨w, hw⟩ := hfc
    obtain ⟨f', hf'⟩ := exists_rankOneTrivialModel_one ψ ℓ' hℓ'
    let Φ := schwartzBruhatComap (oneByOneRow F).symm Φmat
    have hΦ : schwartzBruhatComap (oneByOneRow F) Φ = Φmat :=
      (oneByOneSchwartzEquiv (F := F)).apply_symm_apply Φmat
    refine ⟨R, ⟨w, f', Φ, ?_⟩, hR0⟩
    convert hR.2 using 1
    funext s
    rw [equalRankModelIntegral_rankOne_eq_matrixIntegral, hΦ, hf', one_smul, ← hw]
    rfl
  · intro f f' Φ
    let Φmat := schwartzBruhatComap (oneByOneRow F) Φ
    obtain ⟨ΦmatHat, hFourier, hFE⟩ := hdata.2.2 Φmat
    let Φhat := schwartzBruhatComap (oneByOneRow F).symm ΦmatHat
    have htest : schwartzBruhatComap (oneByOneRow F) Φhat = ΦmatHat := by
      exact (oneByOneSchwartzEquiv (F := F)).apply_symm_apply ΦmatHat
    have hrow : IsRowFourierPair ψ ν Φ Φhat := by
      intro y
      change ΦmatHat ((oneByOneRow F).symm y) = _
      have hy := (hFourier ((oneByOneRow F).symm y)).2
      change ΦmatHat ((oneByOneRow F).symm y) =
        rectangularFourierIntegral ψ ν (fun x => Φ (oneByOneRow F x))
          ((oneByOneRow F).symm y) at hy
      simpa only [rectangularFourierIntegral_oneByOneRow,
        Homeomorph.apply_symm_apply] using hy
    let fc := rankOneModelMatrixCoefficient ψ σ hσ ℓ hℓ ℓ' f f'
    obtain ⟨R, hR⟩ := hdata.1.2.1 Φmat fc
    obtain ⟨RDual, hRDual⟩ := hdata.2.1.2.1 ΦmatHat fc
    have hN := hFE fc R RDual hR hRDual
    refine ⟨Φhat, R, RDual, hrow, ?_, ?_, ?_⟩
    · convert hR.2 using 1
      funext s
      exact equalRankModelIntegral_rankOne_eq_matrixIntegral ψ abv σ ℓ ℓ' f f' Φ s
    · convert hRDual.2 using 1
      funext s
      rw [dualEqualRankModelIntegral_rankOne_eq_matrixIntegral, htest]
      rfl
    · intro s hR hRDual hG
      exact hN.gamma_value_of_regular hq hδ hdata.2.1.2.2.polynomial_ne_zero
        s hR hRDual hG

end Equation

end Langlands.RankinSelberg
