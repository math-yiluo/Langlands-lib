import Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity
import Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffFourier
import Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusProof
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
/-! # Fourier regularity of actual supercuspidal coefficient cutoffs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient
open Langlands.AllField.GodementJacquet

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Geometry


end Geometry

section Cutoff

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {m : ℕ} (hm : 0 < m)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hm

/-- The actual raw Fourier transform of every supercuspidal coefficient cutoff
vanishes at every singular matrix, for the supplied additive Haar measure. -/
theorem supercuspidalCutoffMatrixTest_fourier_singular :
    letI := T.topology
    letI := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V)
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F), ¬ IsUnit A →
      rectangularFourierIntegral ψ ν
        (supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v) A = 0 := by
  let := T.topology
  let := borel F
  intro ψ ν ρ hρ ℓ hℓ v A hA
  obtain ⟨B, c, hB, hstab⟩ := exists_singular_inverseTranspose_stabilizer hm A hA
  exact supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer T (Nat.succ_pos m)
    ψ ν ρ hρ ℓ hℓ (B.conjugateUnipotent c) (hρ.2 B hB c)
    (fun g hg => determinantNorm_eq_one_of_mem_conjugateUnipotent T B c hg)
    A hstab v

/-- With the supplied scalar self-dual measure, every actual coefficient cutoff
belongs to the support-defined Fourier-regular matrix test space. -/
theorem supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := (padicLatticeGeometry F T).1
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (hsd : IsSelfDual ψ ν)
      (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V),
      supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v ∈
        fourierRegularMatrixTests (m + 1) ψ ν hsd := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := (padicLatticeGeometry F T).1
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ ν hsd ρ hρ ℓ hℓ v
  refine ⟨?_, ?_⟩
  · exact supercuspidalCutoffMatrixTest_singular T (Nat.succ_pos m) ρ hρ ℓ hℓ v
  · intro A hA
    exact (rectangularFourierEquiv_apply ψ ν (m + 1) (m + 1) hsd
      (supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v) A).trans
        (supercuspidalCutoffMatrixTest_fourier_singular T hm ψ ν ρ hρ ℓ hℓ v A hA)

end Cutoff

end Langlands.AllField.GodementJacquet
