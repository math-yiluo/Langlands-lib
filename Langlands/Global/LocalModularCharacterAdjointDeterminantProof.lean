import Langlands.Global.LocalModularCharacter.AdjointBound
import Langlands.Global.LocalModularCharacter.PlaceGlue
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology

/-! # The local modular character is the normalized absolute value of `det Ad`

Proof of `Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`.
See `LocalModularCharacterAdjointDeterminantProof.md`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Langlands.GroupScheme
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Global.PlaceGroupPoints

open LocalModularCharacter

attribute [local instance] identityChartTopology identityChartTopologicalRing
  identityChartPointsTopology identityChartPointsTopologicalGroup

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- At every place, the modular character of the local point group is at most the normalized
absolute value of the adjoint determinant character. -/
theorem modularCharacter_le_localCharacterNorm (hG : Smooth G.X.hom) (i : Place F)
    (g : PlaceGroupPoints F G i) :
    Measure.modularCharacter g ≤
      (AdelicGroupPoints.localCharacterNorm F G
        (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul i g : ℝ≥0) := by
  rcases i with w | v
  · let : NontriviallyNormedField w.Completion :=
      Langlands.AlgebraicGeometry.PointTopology.infiniteCompletionNontriviallyNormedField w
    obtain ⟨_, _⟩ := exists_normedSpace_real_infiniteCompletion w
    have : ProperSpace w.Completion := FiniteDimensional.proper_real _
    have : LocallyCompactSpace (G.affinePoints (CommAlgCat.of F w.Completion)) :=
      PlaceGroupPoints.locallyCompactSpace F G (.inl w)
    have : T2Space (G.affinePoints (CommAlgCat.of F w.Completion)) :=
      PlaceGroupPoints.t2Space F G (.inl w)
    have : SecondCountableTopology (G.affinePoints (CommAlgCat.of F w.Completion)) :=
      PlaceGroupPoints.secondCountableTopology F G (.inl w)
    let : MeasurableSpace (G.affinePoints (CommAlgCat.of F w.Completion)) :=
      PlaceGroupPoints.measurableSpace F G (.inl w)
    have : BorelSpace (G.affinePoints (CommAlgCat.of F w.Completion)) :=
      PlaceGroupPoints.borelSpace F G (.inl w)
    have h := modularCharacter_le_of_adjoint_real G (K := w.Completion) hG g
      (AdelicGroupPoints.localCharacterNorm F G
        (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul (.inl w) g : ℝ≥0) ?_
    · exact h
    · intro d m b A hA
      exact @addEquivAddHaarChar_placeLinear_eq_localCharacterNorm F _ _ G _ _ (.inl w) g d m b
        A hA
  · let : NontriviallyNormedField (FiniteCompletion F v) :=
      Valued.toNontriviallyNormedField (FiniteCompletion F v) (WithZero (Multiplicative ℤ))
    have : LocallyCompactSpace (FiniteCompletion F v) :=
      placeCompletion.locallyCompactSpace F (.inr v)
    have : ProperSpace (FiniteCompletion F v) :=
      ProperSpace.of_locallyCompactSpace (FiniteCompletion F v)
    have : LocallyCompactSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
      PlaceGroupPoints.locallyCompactSpace F G (.inr v)
    have : T2Space (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
      PlaceGroupPoints.t2Space F G (.inr v)
    have : SecondCountableTopology (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
      PlaceGroupPoints.secondCountableTopology F G (.inr v)
    let : MeasurableSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
      PlaceGroupPoints.measurableSpace F G (.inr v)
    have : BorelSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))) :=
      PlaceGroupPoints.borelSpace F G (.inr v)
    have h := modularCharacter_le_of_adjoint_ultrametric G (K := FiniteCompletion F v) hG g
      (AdelicGroupPoints.localCharacterNorm F G
        (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul (.inr v) g : ℝ≥0) ?_
    · exact h
    · intro d m b A hA
      exact @addEquivAddHaarChar_placeLinear_eq_localCharacterNorm F _ _ G _ _ (.inr v) g d m b
        A hA

/-- **Local modular character formula.** At every place `i` of a number field `F`, the modular
character of `G(F_i)` for a smooth affine group scheme `G` of finite type over `F` is the
normalized absolute value of the determinant of the adjoint representation. -/
theorem localModularCharacterAdjointDeterminant :
    LocalModularCharacterAdjointDeterminantStatement.{u} := by
  intro F _ _ G _ _ hG i g
  have hle := modularCharacter_le_localCharacterNorm F G hG i
  set N := AdelicGroupPoints.localCharacterNorm F G
    (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul i
  have hΔ : Measure.modularCharacter g * Measure.modularCharacter g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hN : (N g : ℝ≥0) * (N g⁻¹ : ℝ≥0) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine le_antisymm (hle g) ?_
  calc (N g : ℝ≥0) = N g * (Measure.modularCharacter g * Measure.modularCharacter g⁻¹) := by
        rw [hΔ, mul_one]
    _ ≤ N g * (Measure.modularCharacter g * N g⁻¹) := by gcongr; exact hle g⁻¹
    _ = Measure.modularCharacter g * (N g * N g⁻¹) := by ring
    _ = Measure.modularCharacter g := by rw [hN, mul_one]

end Langlands.Global.PlaceGroupPoints
