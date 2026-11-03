import Langlands.GroupScheme.Rational.StandardLeviCenterStatements
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Split-component points in the actual standard Levi subgroup

For a standard Levi represented by `j : M ⟶ G` and a homomorphism `a : H ⟶ M`,
typically the split component `A_M`, the point map `H(F) → M(F) → standardLeviPoints`
is `rationalPoints.map a` followed by `standardLeviRationalPointsEquiv`. Its values are
central when `a` is central. It is continuous for the canonical topology on `H(F)` and
both the canonical topology on `M(F)` and the topology on `standardLeviPoints` inherited
from `G(F)`. The topology comparison `StandardLeviPointTopologyComparison` is not used.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

section Affine

variable {F : Type u} [Field F] {M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- A split component is affine: its source is a split torus. -/
theorem IsSplitComponent.isAffine {a : A.toGrp ⟶ M} (ha : IsSplitComponent a) :
    IsAffine A.toGrp.X.left :=
  have := ha.isCentralSplitTorus.isSplitSubtorus.1.isAffineHom
  isAffine_of_isAffineHom A.toGrp.X.hom

end Affine

section PointMap

variable {F : Type u} [Field F] [TopologicalSpace F]
  {H M : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] [IsAffine M.X.left]

/-- The point map of a homomorphism is continuous for the canonical point topologies. -/
theorem continuous_rationalPoints_map (a : H ⟶ M) :
    letI : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
    letI : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
    Continuous (rationalPoints.map a) :=
  continuous_rationalPointMap F a.hom.hom

end PointMap

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))
  {M : GroupScheme (Spec (CommRingCat.of F))} (j : M ⟶ G)
  (hj : (standardLevi i ν J).IsRepresentedBy j)
  {H : GroupScheme (Spec (CommRingCat.of F))} (a : H ⟶ M)

/-- The actual point map `H(F) → M(F) → standardLeviPoints`: the points of `a` followed by
the explicit identification of `M(F)` with the standard Levi subgroup of `G(F)`. -/
def splitComponentLeviPointsMap : rationalPoints H →* standardLeviPoints i ν J :=
  (standardLeviRationalPointsEquiv i ν J j hj).toMonoidHom.comp (rationalPoints.map a)

@[simp] theorem splitComponentLeviPointsMap_val (x : rationalPoints H) :
    (splitComponentLeviPointsMap i ν J j hj a x : rationalPoints G) =
      rationalPoints.map j (rationalPoints.map a x) := rfl

/-- The map factors through `M(F)` and `standardLeviRationalPointsEquiv`. -/
theorem splitComponentLeviPointsMap_apply (x : rationalPoints H) :
    splitComponentLeviPointsMap i ν J j hj a x =
      standardLeviRationalPointsEquiv i ν J j hj (rationalPoints.map a x) := rfl

/-- For central `a`, the map is the existing central point map followed by the inclusion
of the abstract center. -/
theorem splitComponentLeviPointsMap_eq_standardLeviCentralRationalPointsMap
    (ha : IsCentral a) (x : rationalPoints H) :
    splitComponentLeviPointsMap i ν J j hj a x =
      (standardLeviCentralRationalPointsMap i ν J j hj a ha x : standardLeviPoints i ν J) :=
  rfl

/-- Centrality: a central `a` sends `H(F)` into the center of the standard Levi subgroup. -/
theorem splitComponentLeviPointsMap_mem_center (ha : IsCentral a) (x : rationalPoints H) :
    splitComponentLeviPointsMap i ν J j hj a x ∈ Subgroup.center (standardLeviPoints i ν J) :=
  (standardLeviCentralRationalPointsMap i ν J j hj a ha x).property

/-- The points of a split component are central in the standard Levi subgroup. -/
theorem IsSplitComponent.splitComponentLeviPointsMap_mem_center
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (x : rationalPoints A.toGrp) :
    splitComponentLeviPointsMap i ν J j hj a x ∈ Subgroup.center (standardLeviPoints i ν J) :=
  GroupScheme.splitComponentLeviPointsMap_mem_center i ν J j hj a
    ha.isCentralSplitTorus.isCentral x

variable [TopologicalSpace F]

/-- Continuity into the topology on `standardLeviPoints` inherited from the canonical
topology of `G(F)`. The proof uses the actual point map of `a ≫ j`, not a topology
comparison for the equivalence. -/
theorem continuous_splitComponentLeviPointsMap [IsAffine G.X.left] [IsAffine H.X.left] :
    letI : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
    letI : TopologicalSpace (standardLeviPoints i ν J) := standardLeviPointTopology i ν J
    Continuous (splitComponentLeviPointsMap i ν J j hj a) := by
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
  let : TopologicalSpace (standardLeviPoints i ν J) := standardLeviPointTopology i ν J
  exact continuous_induced_rng.mpr (continuous_rationalPointMap F (a ≫ j).hom.hom)

end Langlands.GroupScheme
