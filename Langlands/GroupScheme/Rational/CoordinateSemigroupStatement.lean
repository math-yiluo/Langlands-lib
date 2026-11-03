import Langlands.GroupScheme.Rational.CoordinateLieComparisonStatement

/-! # Positive augmentation-weight semigroup comparison targets -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

/-- CGP Example 3.3.2: actual augmentation weights are precisely positive finite
sums of the original intrinsic Lie weights for smooth connected affine groups. -/
def AugmentationLieSemigroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hsm : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (_hconn : ConnectedSpace G.X.left) (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    support b = (AddSubsemigroup.closure (RelativeRoot.actionWeightSupport b ⊤) :
      Set (characterLattice S))

/-- Equivalent support-containment criterion for every additive subsemigroup,
including the empty semigroup; no additive identity is inserted. -/
def AugmentationLieContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hsm : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (_hconn : ConnectedSpace G.X.left) (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    ∀ M : AddSubsemigroup (characterLattice S),
      support b ⊆ M ↔ RelativeRoot.actionWeightSupport b ⊤ ⊆ M

/-- Exact semigroup equality and its containment criterion, without either
semigroup realization or commutator bounds as hypotheses. -/
def CoordinateSemigroupComparisonStatement : Prop :=
  AugmentationLieSemigroupStatement.{u} ∧ AugmentationLieContainmentStatement.{u}

end Langlands.GroupScheme.CoordinateWeights
