import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Rational.UnipotentPointsExponent

/-! # Embedding smooth commutative p-torsion groups in vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The vector-group embedding assertion of CGP B.1.10, over an arbitrary
field of positive characteristic, with the exponent imposed on all tests.
No connectedness or unipotence assumption is required. -/
def SmoothCommutativePTorsionVectorEmbeddingStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : CommGroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom →
    HasUniformPowerExponent G.toGrp p →
      ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : G.toGrp ⟶ V),
        IsClosedSubgroup j ∧ IsVectorGroup V

end Langlands.GroupScheme.RelativeRoot
