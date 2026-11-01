import Langlands.Representation.GodementJacquet.SupercuspidalMonomialComparison
import Langlands.Representation.GodementJacquet.RegularMatrixConvolutionExchange
import Langlands.Representation.Classification.SupercuspidalInverseTranspose

/-! # The supercuspidal equation on Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fourierRegularEquationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fourierRegularEquationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance fourierRegularEquationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance fourierRegularEquationT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance fourierRegularEquationDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance fourierRegularEquationMeasurable : MeasurableSpace F.Carrier := borel _
local instance fourierRegularEquationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance fourierRegularEquationGLMeasurable (m : ℕ) :
    MeasurableSpace (GeneralLinear (m + 1) F.Carrier) := borel _
local instance fourierRegularEquationGLBorel (m : ℕ) :
    BorelSpace (GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual inverse-transpose zeta operator at the complementary exponent,
after the actual plus Fourier transform on the Fourier-regular subspace. -/
def fourierRegularInverseTransposeZetaOperator
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (m + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ) :
    fourierRegularMatrixTests (m + 1) ψ ν hsd →ₗ[ℂ] Module.End ℂ V :=
  (fourierRegularMatrixZetaOperator F
    (ρ.comp (GeneralLinear.inverseTranspose (m + 1) F.Carrier).toMonoidHom)
      hι ψ ν hsd ((m + 1 : ℕ) - s)).comp
    (fourierRegularMatrixFourierEquiv (m + 1) ψ ν hsd).toLinearMap

@[simp] theorem fourierRegularInverseTransposeZetaOperator_apply
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (m + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) :
    fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
      regularMatrixZetaOperator F
        (ρ.comp (GeneralLinear.inverseTranspose (m + 1) F.Carrier).toMonoidHom)
        hι ((m + 1 : ℕ) - s)
        ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ := rfl

/-- On Fourier-regular tests, the actual supercuspidal functional equation has
one nonzero monomial for all spectral parameters, with no cross premise. -/
theorem exists_monomial_fourierRegular_inverseTranspose
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) :
    ∃ (c : ℂˣ) (k : ℤ), ∀ (s : ℂ)
      (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      fourierRegularInverseTransposeZetaOperator F ρ
          (GeneralLinear.isSupercuspidal_comp_inverseTranspose ρ hρ).1.1 ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint F.canonicalTopologicalData.residueCardinality s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  have hι := GeneralLinear.isSupercuspidal_comp_inverseTranspose ρ hρ
  obtain ⟨c, k, hck⟩ := exists_monomial_scalar_of_fourierRegular_cross F hm ρ hρ hi
    (ρ.comp (GeneralLinear.inverseTranspose (m + 1) F.Carrier).toMonoidHom) hι
    ψ ν hsd ((m + 1 : ℕ) : ℂ) (fun s Φ Ψ => by
      exact (regularMatrixZetaOperator_inverseTranspose_cross F ρ hρ.1.1 hι.1.1
        ψ ν hsd s Φ Ψ).symm)
  exact ⟨c, k, hck⟩

/-- Evaluation of the operator equation gives the literal matrix-integral
equation for every vector and algebraic functional. -/
theorem matrixIntegral_eq_of_fourierRegular_inverseTranspose
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (m + 1) F.Carrier).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s a : ℂ)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd)
    (hFE : fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
      a • fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ)
    (v : V) (ℓ : Module.Dual ℂ V) :
    matrixIntegral F (rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val)
        ((m + 1 : ℕ) - s)
        (fun g => ℓ (ρ (GeneralLinear.inverseTranspose (m + 1) F.Carrier g) v)) =
      a * matrixIntegral F Φ.val s (fun g => ℓ (ρ g v)) := by
  have he := congrArg (fun L : Module.End ℂ V => ℓ (L v)) hFE
  simpa only [fourierRegularInverseTransposeZetaOperator_apply,
    fourierRegularMatrixZetaOperator_apply, LinearMap.smul_apply,
    map_smul, smul_eq_mul, regularMatrixZetaOperator_dual,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using he

end Langlands.GodementJacquet.Padic
