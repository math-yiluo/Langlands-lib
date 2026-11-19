import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.HarmonicAnalysis.Distribution.GeneralLinear
import Langlands.LinearAlgebra.MatrixTransposeConjugateProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonReflectedHaar
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units

/-! # Haar transposition and conjugacy-invariant densities on actual archimedean GL -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.HarmonicAnalysis.Distribution (transposeHomeomorph transposeHomeomorph_coe)

variable (F : Type*) [RCLike F] (n : ℕ)

local notation "GL" => Langlands.GeneralLinear n F

/-- The transpose of every actual archimedean general linear element is conjugate to it. -/
theorem isConj_transpose (g : GL) : IsConj g (transposeHomeomorph n F g) := by
  obtain ⟨a, ha⟩ := Langlands.matrixTransposeConjugate F n g.val
  exact isConj_iff.mpr ⟨a, Units.ext (ha.trans (transposeHomeomorph_coe n F g).symm)⟩

variable [MeasurableSpace (Langlands.GeneralLinear n F)] [BorelSpace (Langlands.GeneralLinear n F)]

local instance : LocallyCompactSpace GL := Units.isOpenEmbedding_val.locallyCompactSpace

variable (μ : Measure (Langlands.GeneralLinear n F)) [μ.IsHaarMeasure] [μ.Regular]

/-- Every regular Haar measure on actual archimedean GL is right invariant. -/
theorem isMulRightInvariant_archimedeanGL : μ.IsMulRightInvariant := by
  have hs (a : Fˣ) : Measure.modularCharacter (Matrix.GeneralLinearGroup.scalar (Fin n) a) = 1 := by
    change Measure.modularCharacterFun _ = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ]
    have he : (fun x : GL => x * Matrix.GeneralLinearGroup.scalar (Fin n) a) =
        (fun x : GL => Matrix.GeneralLinearGroup.scalar (Fin n) a * x) := by
      funext x
      exact (Matrix.GeneralLinearGroup.scalar_commute a x).symm
    have hm : Measure.map (fun x : GL => x * Matrix.GeneralLinearGroup.scalar (Fin n) a) μ = μ := by
      rw [he, map_mul_left_eq_self]
    have hf (ν : Measure GL) [ν.IsHaarMeasure] (hν : ν = μ) :
        Measure.haarScalarFactor ν μ = 1 := by
      subst ν
      exact Measure.haarScalarFactor_self _
    exact hf _ hm
  have ht (g : GL) : Measure.modularCharacterFun g = 1 :=
    RankinSelberg.GeneralLinearUnimodularity.character_eq_one Measure.modularCharacter hs g
  constructor
  intro g
  have : (Measure.map (fun x : GL => x * g) μ).Regular :=
    Measure.Regular.map (μ := μ) (Homeomorph.mulRight g)
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular (Measure.map (fun x : GL => x * g) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, ht, one_smul]

/-- Inversion preserves any regular Haar measure on actual archimedean GL. -/
theorem measurePreserving_inv_archimedeanGL : MeasurePreserving (Inv.inv : GL → GL) μ μ := by
  let _ := isMulRightInvariant_archimedeanGL F n μ
  let _ := Langlands.isInvInvariant_of_isMulRightInvariant μ
  exact Measure.measurePreserving_inv μ

/-- Inverse transpose preserves any regular Haar measure on actual archimedean GL. -/
theorem measurePreserving_inverseTranspose_archimedeanGL :
    MeasurePreserving (Langlands.GeneralLinear.inverseTranspose n F) μ μ :=
  RankinSelberg.measurePreserving_involutive_automorphism
    (Langlands.GeneralLinear.inverseTransposeContinuous n F)
    (Langlands.GeneralLinear.inverseTranspose_involutive n F) μ

/-- Ordinary matrix transpose preserves any regular Haar measure on actual archimedean GL. -/
theorem measurePreserving_transpose_archimedeanGL :
    MeasurePreserving (transposeHomeomorph n F) μ μ :=
  (measurePreserving_inverseTranspose_archimedeanGL F n μ).comp
    (measurePreserving_inv_archimedeanGL F n μ)

variable (φ : Langlands.GeneralLinear n F → ℂ)

/-- Pair a scalar density with a test function by integration against left Haar. For locally
integrable densities and smooth compact tests this is the ordinary integral pairing. -/
def densityIntegral (f : GL → ℂ) : ℂ := ∫ g, f g * φ g ∂μ

/-- A pointwise conjugation-invariant density gives the same Haar integral after transposition
of the test function. -/
theorem densityIntegral_transpose (hφ : ∀ a g : GL, φ (a * g * a⁻¹) = φ g)
    (f : GL → ℂ) : densityIntegral F n μ φ (fun g => f (transposeHomeomorph n F g)) =
      densityIntegral F n μ φ f := by
  have hs (g : GL) : φ (transposeHomeomorph n F g) = φ g := by
    obtain ⟨a, ha⟩ := isConj_iff.mp (isConj_transpose F n g)
    rw [← ha, hφ]
  let e := (transposeHomeomorph n F).toMeasurableEquiv
  have he : MeasurePreserving e μ μ := measurePreserving_transpose_archimedeanGL F n μ
  calc
    _ = ∫ g, f (e g) * φ (e g) ∂μ := by
      unfold densityIntegral
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => congrArg (f (e g) * ·) (hs g).symm
    _ = _ := he.integral_comp' (fun g => f g * φ g)

end Langlands.Archimedean
