import Langlands.GroupScheme.Rational.CentralSmoothQuotientOrbitReduction
import Langlands.GroupScheme.Rational.CentralVectorClassificationReduction
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Central vector and quotient consequences of closed-subgroup unipotence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The exact central smooth quotient target, with all structural premises
discharged by published proofs. -/
theorem centralSmoothQuotient : CentralSmoothQuotientStatement.{u} :=
  centralSmoothQuotient_of_closedSubgroup unipotentClosedSubgroup

/-- Choose actual central vector-subgroup data using only the remaining
classification and torus-linearization propositions. -/
def centralStableVectorSubgroupOfVectorInputs
    (hclass : CommutativeVectorClassificationStatement.{u})
    (hlin : SplitTorusVectorLinearizationStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    CentralStableVectorSubgroupData b :=
  centralStableVectorSubgroupOfClassification
    hclass hlin unipotentClosedSubgroup k G S hS b hG hU

/-- Closed-subgroup unipotence is no longer a premise of the conditional
central-vector target. -/
theorem centralStableVectorSubgroup_of_vectorInputs
    (hclass : CommutativeVectorClassificationStatement.{u})
    (hlin : SplitTorusVectorLinearizationStatement.{u}) :
    CentralStableVectorSubgroupStatement.{u} :=
  centralStableVectorSubgroup_of_classification hclass hlin unipotentClosedSubgroup

/-- The combined central-vector and quotient target now retains exactly the
classification and whole-vector torus-linearization propositions. -/
theorem centralVectorQuotient_of_vectorInputs
    (hclass : CommutativeVectorClassificationStatement.{u})
    (hlin : SplitTorusVectorLinearizationStatement.{u}) :
    CentralVectorQuotientStatement.{u} :=
  ⟨centralStableVectorSubgroup_of_vectorInputs hclass hlin, centralSmoothQuotient⟩

end Langlands.GroupScheme.RelativeRoot
