import Langlands.BruhatTits.RationalPoints.BoundedSubgroupNormKernel
import Langlands.GroupScheme.Reductive.Basic

/-! # Boundedness of normalizers inside the rational norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.RationalPoints

/-- KP Proposition 2.2.16 in the nonarchimedean local-field case: the
normalizer of a bounded open subgroup, intersected with the common kernel
of the actual rational-character norms, is algebraically bounded. -/
def BoundedOpenNormalizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ H : Subgroup (rationalPoints G),
      IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G)) →
      IsOpen (H : Set (rationalPoints G)) →
      IsAlgebraicallyBounded F G.X
        ((Subgroup.normalizer (H : Set (rationalPoints G)) ⊓
          Langlands.Plancherel.rationalCommonNormKernel G) : Set (rationalPoints G))

end Langlands.BruhatTits.RationalPoints
