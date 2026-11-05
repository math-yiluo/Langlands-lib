import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicCharacterLog
import Langlands.GroupScheme.Lie.AdjointDeterminantCharacter
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # The analytic modular character on actual adelic group points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

/-- The analytic modulus of the actual adelic group is the normalized idele norm
of its actual rational adjoint determinant character. -/
def AdelicModularCharacterAdjointDeterminantStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    Smooth G.X.hom → ConnectedSpace G.X.left →
      ∀ g : AdelicGroupPoints F G,
        Measure.modularCharacter g =
          (characterNorm F G
            (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul g : ℝ≥0)

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Once the analytic comparison is proved, algebraic determinant triviality
makes the actual ambient modular character one. -/
theorem modularCharacter_eq_one_of_adjointDeterminant_eq_zero
    (hcompare : ∀ g : AdelicGroupPoints F G,
      Measure.modularCharacter g =
        (characterNorm F G
          (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul g : ℝ≥0))
    (hdet : Langlands.GroupScheme.Lie.adjointDeterminantCharacter G = 0)
    (g : AdelicGroupPoints F G) :
    Measure.modularCharacter g = 1 := by
  rw [hcompare g, hdet, characterNorm_zero, Units.val_one]

/-- The fixed Haar measure is right invariant after the analytic comparison
and algebraic determinant triviality have both been supplied. -/
theorem haarRightInvariant_of_adjointDeterminant_eq_zero
    (hcompare : ∀ g : AdelicGroupPoints F G,
      Measure.modularCharacter g =
        (characterNorm F G
          (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul g : ℝ≥0))
    (hdet : Langlands.GroupScheme.Lie.adjointDeterminantCharacter G = 0) :
    (Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant := by
  constructor
  intro g
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
  change Measure.modularCharacter g • Measure.haar = Measure.haar
  rw [modularCharacter_eq_one_of_adjointDeterminant_eq_zero F G hcompare hdet g, one_smul]

end Langlands.Global.AdelicGroupPoints
