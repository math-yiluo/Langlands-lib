import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothGodementInvariants
import Langlands.Cohomology.SmoothGodement.EdgeSpatial

/-! # Proper rational pullback of the existing all-degree invariants edge -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementCohomology.Spatial
open Langlands.Cohomology.SmoothGodementComparison

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.SmoothCohomology

variable (X : ρ.OpenSubgroupTransport) [HasStableNeighbourhoods G X.InducedSpectrum]

/-- The existing full coefficient invariants edge, as an arrow of coefficient functors. -/
def godementInvariantsEdgeArrow (q : ℕ) :
    Arrow (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  Arrow.mk (godementInvariantsEdge (R := R) X q)

end OpenSubgroupTransport.SmoothCohomology

namespace OpenSubgroupTransport.Hom

open SmoothCohomology

variable {X Y Z : ρ.OpenSubgroupTransport}
  [HasStableNeighbourhoods G X.InducedSpectrum]
  [HasStableNeighbourhoods G Y.InducedSpectrum]
  [HasStableNeighbourhoods G Z.InducedSpectrum]

/-- The previously defined invariants edge commutes with the actual proper rational pullbacks. -/
@[reassoc]
theorem godementInvariantsEdge_pullback (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) :
    godementInvariantCohomologyPullbackNatTrans (R := R) f hf q ≫ godementInvariantsEdge X q =
      godementInvariantsEdge Y q ≫
        Functor.whiskerRight (godementCohomologyPullbackNatTrans f hf q) (smoothInvariants R G) :=
  coefficientInvariantsEdge_pullback f.inducedMap f.inducedMap_smul hf q

/-- Proper pullback of the existing edge retains both original all-degree cohomology maps. -/
def godementInvariantsEdgePullback (f : X ⟶ Y) (hf : IsProperMap f.inducedMap) (q : ℕ) :
    godementInvariantsEdgeArrow (R := R) Y q ⟶ godementInvariantsEdgeArrow X q :=
  coefficientInvariantsEdgePullback f.inducedMap f.inducedMap_smul hf q

@[simp]
theorem godementInvariantsEdgePullback_left (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) :
    (godementInvariantsEdgePullback (R := R) f hf q).left =
      godementInvariantCohomologyPullbackNatTrans f hf q := rfl

@[simp]
theorem godementInvariantsEdgePullback_right (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap) (q : ℕ) :
    (godementInvariantsEdgePullback (R := R) f hf q).right =
      Functor.whiskerRight (godementCohomologyPullbackNatTrans f hf q) (smoothInvariants R G) := rfl

@[simp]
theorem godementInvariantsEdgePullback_id (q : ℕ) :
    godementInvariantsEdgePullback (R := R) (𝟙 X) (isProperMap_inducedMap_id X) q =
      𝟙 (godementInvariantsEdgeArrow X q) := by
  apply Arrow.hom_ext
  · exact godementInvariantCohomologyPullbackNatTrans_id q
  · change Functor.whiskerRight (godementCohomologyPullbackNatTrans _ _ _) _ = _
    rw [godementCohomologyPullbackNatTrans_id]
    rfl

/-- Composition is strictly contravariant in the arrow category, in every degree. -/
theorem godementInvariantsEdgePullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) (q : ℕ) :
    godementInvariantsEdgePullback (R := R) (f ≫ g)
        (isProperMap_inducedMap_comp f g hf hg) q =
      godementInvariantsEdgePullback g hg q ≫ godementInvariantsEdgePullback f hf q := by
  apply Arrow.hom_ext
  · exact godementInvariantCohomologyPullbackNatTrans_comp f g hf hg q
  · change Functor.whiskerRight (godementCohomologyPullbackNatTrans _ _ _) _ = _
    rw [godementCohomologyPullbackNatTrans_comp f g hf hg q]
    rfl

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
