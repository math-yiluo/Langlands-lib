import Langlands.Global.AdelicLocalCharacterNorm
import Langlands.Global.AdelesSecondCountable
import Langlands.GroupScheme.Lie.AdjointDeterminantCharacter
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Local analytic modulus on actual completion-valued point groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

namespace placeCompletion

/-- Every actual number-field completion is second countable. -/
instance secondCountableTopology :
    (i : Place F) → SecondCountableTopology (placeCompletion F i)
  | .inl w => infiniteCompletion_secondCountableTopology F w
  | .inr v => finiteCompletion_secondCountableTopology F v

end placeCompletion

namespace PlaceGroupPoints

/-- Finite-type affine points over an actual completion are second countable. -/
instance secondCountableTopology
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (i : Place F) :
    SecondCountableTopology (PlaceGroupPoints F G i) :=
  G.affinePointsSecondCountableTopology (placeCompletion F i)

/-- The analytic modulus at each actual completion is the normalized absolute
value of the full algebraic adjoint determinant. -/
def LocalModularCharacterAdjointDeterminantStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    Smooth G.X.hom →
      ∀ (i : Place F) (g : PlaceGroupPoints F G i),
        Measure.modularCharacter g =
          (AdelicGroupPoints.localCharacterNorm F G
            (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul i g : ℝ≥0)

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (i : Place F)

/-- A pointwise analytic comparison gives the corresponding scaling of the
existing fixed local Haar measure under positive right translation. -/
theorem map_mul_right_haar_of_adjointDeterminant_comparison
    (hcompare : ∀ g : PlaceGroupPoints F G i,
      Measure.modularCharacter g =
        (AdelicGroupPoints.localCharacterNorm F G
          (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul i g : ℝ≥0))
    (g : PlaceGroupPoints F G i) :
    Measure.map (fun x => x * g) (Measure.haar : Measure (PlaceGroupPoints F G i)) =
      (AdelicGroupPoints.localCharacterNorm F G
        (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul i g : ℝ≥0) •
          (Measure.haar : Measure (PlaceGroupPoints F G i)) := by
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
  change Measure.modularCharacter g • Measure.haar = _
  rw [hcompare g]

end PlaceGroupPoints

end Langlands.Global
