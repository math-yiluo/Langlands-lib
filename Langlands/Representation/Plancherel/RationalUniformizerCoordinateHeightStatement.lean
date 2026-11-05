import Langlands.Representation.Plancherel.RationalModerateGrowthStatement
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Coordinate height of actual uniformizer charts -/

noncomputable section

universe u uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation CocharacterUniformizer

/-- A character positive on every supplied generator bounds the total natural
coordinate height by a power of any actual closed matrix embedding. -/
def RationalUniformizerCoordinateHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
    IsClosedSubgroup i →
    ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
      (ρ : MatrixRepresentation G n), IsClosedSubgroup ρ →
      ∀ (I : Type uI) [Fintype I] (x : I → cocharacterLattice S)
        (α : characterLattice S),
        (∀ j, 0 < latticePairing S α (x j)) →
        ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ m : I → ℕ,
          (LocalField.residueCardinality F : ℝ) ^ (∑ j, m j) ≤
            c * rationalMatrixNorm F ρ
              (rationalPoints.map i
                (latticeSection F S (.ofAdd (∑ j, m j • x j)))) ^ d

end Langlands.Plancherel
