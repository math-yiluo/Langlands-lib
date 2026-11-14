import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
/-! # Compact and finite-order symmetries in actual matrix Fourier tests -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis


end Langlands.AllField.HarmonicAnalysis

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- A finite-order matrix has determinant norm one. -/
theorem determinantNorm_eq_one_of_pow_eq_one {r m : ℕ}
    (g : GeneralLinear r F) (hm : m ≠ 0) (hg : g ^ m = 1) :
    T.determinantNorm r g = 1 := by
  apply Units.ext
  apply (pow_eq_one_iff_of_nonneg
    (show (0 : ℝ≥0) ≤ (T.determinantNorm r g : ℝ≥0) from zero_le) hm).mp
  have h := congrArg (fun a => (T.determinantNorm r a : ℝ≥0)) hg
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using h

/-- Every actual permutation matrix has determinant norm one. -/
theorem determinantNorm_permutation (r : ℕ) (σ : Equiv.Perm (Fin r)) :
    T.determinantNorm r (GeneralLinear.permutation r F σ) = 1 := by
  apply T.determinantNorm_eq_one_of_pow_eq_one _
    (Nat.ne_zero_of_lt (orderOf_pos σ))
  rw [← map_pow, pow_orderOf_eq_one, map_one]

/-- The unsigned long Weyl representative has determinant norm one. -/
theorem determinantNorm_weylLong (r : ℕ) :
    T.determinantNorm r (GeneralLinear.weylLong r F) = 1 :=
  T.determinantNorm_permutation r Fin.revPerm

end Langlands.LocalFieldData

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- A left-right symmetry of a test transfers to the corresponding
inverse-transpose symmetry of its actual full Fourier partner. -/
theorem padicMatrixFourierPair_leftRight_invariant
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (A B : GeneralLinear (n + 1) F),
      T.determinantNorm (n + 1) A = 1 → T.determinantNorm (n + 1) B = 1 →
      ∀ Φ ΦHat : MatrixTestFunction n F,
      MatrixFourierPair ψ ν Φ ΦHat →
      (∀ Y, Φ (A.val * Y * B.val) = Φ Y) →
      ∀ X, ΦHat ((GeneralLinear.inverseTranspose (n + 1) F A).val * X *
        (GeneralLinear.inverseTranspose (n + 1) F B).val) = ΦHat X := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  intro ψ ν A B hA hB Φ ΦHat hpair hinv X
  calc
    _ = rectangularFourierIntegral ψ ν Φ _ := (hpair _).2
    _ = rectangularFourierIntegral ψ ν (fun Y => Φ (A.val * Y * B.val)) X :=
      (padicRectangularFourierIntegral_leftRight F T (n + 1) (n + 1)
        ψ ν A B hA hB Φ X).symm
    _ = rectangularFourierIntegral ψ ν Φ X := by
      congr 1
      funext Y
      exact hinv Y
    _ = _ := (hpair X).2.symm

/-- Left invariance under a compact subgroup becomes left invariance of the
Fourier partner under its actual inverse-transpose image. -/
theorem padicMatrixFourierPair_compact_left_invariant
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (J : Subgroup (GeneralLinear (n + 1) F)),
      IsCompact (J : Set (GeneralLinear (n + 1) F)) →
      ∀ Φ ΦHat : MatrixTestFunction n F,
      MatrixFourierPair ψ ν Φ ΦHat →
      Φ ∈ rectangularLeftInvariantTests J →
      ΦHat ∈ rectangularLeftInvariantTests
        (J.map (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  intro ψ ν J hJ Φ ΦHat hpair hinv
  rintro A ⟨g, hg, rfl⟩ X
  have h := padicMatrixFourierPair_leftRight_invariant F T n ψ ν g 1
    (T.determinantNorm_eq_one_of_mem_compact (n + 1) J hJ g hg)
    (map_one _) Φ ΦHat hpair (by
      intro Y
      simpa only [Units.val_one, Matrix.mul_one] using hinv g hg Y) X
  simpa only [map_one, Units.val_one, Matrix.mul_one, MulEquiv.coe_toMonoidHom] using h

end Langlands.AllField.GodementJacquet
