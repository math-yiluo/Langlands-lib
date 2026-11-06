import Langlands.GroupScheme.Rational.RootGeneratedWeylRepresentatives
import Langlands.GroupScheme.Rational.PositiveRootStabilizerAveraging
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Relative root systems from opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

/-- Opposite-pair existence supplies integral reflections, and the
unconditional positive-root stabilizer theorem supplies generation and
faithfulness on the actual relative-root span. -/
theorem RelativeRoot.hasRelativeRootSystem_of_hasOppositeFactorPairs
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) :
    HasRelativeRootSystem i := by
  let : Smooth G.X.hom := hG.smooth
  let D := RelativeRootReflectionData.ofOppositeFactorPairs i hi.isSplitSubtorus.1 hE
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  exact D.hasRelativeRootSystem_of_positive_stabilizer hi.isSplitSubtorus.1
    (hi.isSplitSubtorus.1.finite_relativeRoots i) hν
    (hasTrivialPositiveRootStabilizer i hG hi hν)

/-- The exact global rank-one proposition implies the exact global
relative-root-system proposition. Rank-one existence remains a premise. -/
theorem relativeRootSystemStatement_of_rootRankOneFactorizationStatement
    (hRank : RootRankOneFactorizationStatement.{u}) :
    RelativeRootSystemStatement.{u} := by
  intro k _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hE : RelativeRoot.HasOppositeFactorPairs i := by
    intro a ha x hx hx1
    exact (hRank k G hG T i hi a ha x hx hx1).1.exists
  exact RelativeRoot.hasRelativeRootSystem_of_hasOppositeFactorPairs i hG hi hE

/-- Rank-one factorization suffices for the full relative-root-system input.
This is a conditional reduction, not an existence theorem for factor pairs. -/
def RootRankOneRootSystemReductionStatement : Prop :=
  RootRankOneFactorizationStatement.{u} → RelativeRootSystemStatement.{u}

theorem rootRankOneRootSystemReduction : RootRankOneRootSystemReductionStatement.{u} :=
  relativeRootSystemStatement_of_rootRankOneFactorizationStatement

end Langlands.GroupScheme
