import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero

/-!
# The row and matrix Fourier transforms in dimension one

The last-row identification of a `1 × 1` matrix preserves the product of the
supplied scalar measure. It identifies the plus transpose matrix Fourier
transform with the plus row Fourier transform, with no change of normalization.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF

section Fourier

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

/-- Pullback through the unique row is a linear equivalence of the actual
Schwartz–Bruhat spaces. -/
def oneByOneSchwartzEquiv :
    SchwartzBruhat (Fin 1 → F) ≃ₗ[ℂ] GodementJacquet.MatrixTestFunction 0 F where
  toFun := schwartzBruhatComap (oneByOneRow F)
  invFun := schwartzBruhatComap (oneByOneRow F).symm
  left_inv Φ := by
    apply Subtype.ext
    funext x
    exact congrArg Φ ((oneByOneRow F).apply_symm_apply x)
  right_inv Φ := by
    apply Subtype.ext
    funext x
    exact congrArg Φ ((oneByOneRow F).symm_apply_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalRing F] [BorelSpace F] in
/-- The last row of a `1 × 1` matrix preserves the exact supplied product measure. -/
theorem oneByOneRow_measurePreserving (ν : AdditiveHaarMeasure F) :
    MeasurePreserving (oneByOneRow F) (rectangularMeasure ν 1 1) (rowMeasure ν 1) := by
  exact measurePreserving_piUnique (fun _ : Fin 1 => rowMeasure ν 1)

omit [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F] in
/-- The plus transpose pairing becomes the row pairing in dimension one. -/
theorem rectangularPairing_oneByOneRow (x y : Matrix (Fin 1) (Fin 1) F) :
    rectangularPairing x y = rowPairing (oneByOneRow F x) (oneByOneRow F y) := by
  change (∑ i : Fin 1, ∑ j : Fin 1, x i j * y i j) =
    ∑ i : Fin 1, x 0 i * y 0 i
  simp only [Fin.sum_univ_one]

omit [IsTopologicalRing F] [BorelSpace F] in
/-- The raw matrix and row Fourier integrals agree under the last-row map.
The assertion applies even before restricting the input to Schwartz functions. -/
theorem rectangularFourierIntegral_oneByOneRow (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F) (f : (Fin 1 → F) → ℂ)
    (y : Matrix (Fin 1) (Fin 1) F) :
    rectangularFourierIntegral ψ ν (fun x => f (oneByOneRow F x)) y =
      rowFourierIntegral ψ ν 1 f (oneByOneRow F y) := by
  unfold rectangularFourierIntegral rowFourierIntegral
  simp_rw [rectangularPairing_oneByOneRow]
  calc
    _ = ∫ x, f x * ψ.complex (rowPairing x (oneByOneRow F y)) ∂rowMeasure ν 1 :=
      (oneByOneRow_measurePreserving ν).integral_comp
        (MeasurableEquiv.piUnique (fun _ : Fin 1 => Fin 1 → F)).measurableEmbedding _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _

omit [BorelSpace F] in
/-- Pullback of two row tests is a matrix Fourier pair precisely when the
original tests form a row Fourier pair, for the same character and measure. -/
theorem matrixFourierPair_oneByOneRow_iff (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F) [SigmaFinite ν.measure]
    [BorelSpace (Matrix (Fin 1) (Fin 1) F)]
    (Φ ΦHat : SchwartzBruhat (Fin 1 → F)) :
    GodementJacquet.MatrixFourierPair ψ ν
        (schwartzBruhatComap (oneByOneRow F) Φ)
        (schwartzBruhatComap (oneByOneRow F) ΦHat) ↔
      IsRowFourierPair ψ ν Φ ΦHat := by
  constructor
  · intro h y
    have hy := (h ((oneByOneRow F).symm y)).2
    change ΦHat ((oneByOneRow F) ((oneByOneRow F).symm y)) =
      rectangularFourierIntegral ψ ν (fun x => Φ (oneByOneRow F x))
        ((oneByOneRow F).symm y) at hy
    simpa only [rectangularFourierIntegral_oneByOneRow,
      Homeomorph.apply_symm_apply] using hy
  · intro h y
    refine ⟨rectangularFourierIntegrand_integrable ψ ν _ y, ?_⟩
    change ΦHat (oneByOneRow F y) =
      rectangularFourierIntegral ψ ν (fun x => Φ (oneByOneRow F x)) y
    simpa only [rectangularFourierIntegral_oneByOneRow]
      using h (oneByOneRow F y)

end Fourier

end Langlands.RankinSelberg
