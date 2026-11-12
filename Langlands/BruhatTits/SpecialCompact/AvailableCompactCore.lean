import Langlands.BruhatTits.SpecialCompact.WeylRepresentatives
import Langlands.BruhatTits.SpecialCompact.AvailableBasisStatement
import Langlands.BruhatTits.SpecialCompact.InheritedNormalBasis
import Langlands.AlgebraicGeometry.PointTopology.RationalPointEvaluation
import Langlands.Geometry.Building.SpecialPointGlobalFixedLocus
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Geometry.Building.NormalizerApartmentActionKernel
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.Geometry.Building.MetricRealizationProof
import Langlands.Geometry.Metric.KPBoundedSetStabilizerProof
import Langlands.Geometry.Metric.KPCompleteNPCGeodesicProof
import Langlands.BruhatTits.RationalPoints.BoundedSubgroupNormKernel

/-!
# Compact core of the simultaneous-basis target

The bounded/compact maximality and Weyl-representative consequences at the same
special point. The concrete reflection and compact-orbit arguments are adapted
from Worker 102 and Worker 3557's published available-Iwasawa proof.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact

section Datum
variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G)

section Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- The compact-orbit part of the public fixed-point draft by Worker 3557. -/
private theorem compact_subgroup_fixes
    (M : B.toValuationBuildingData.MetricRealization)
    (H : Subgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    ∃ y : B.ReducedBuilding, ∀ h ∈ H, h • y = y := by
  let : MetricSpace B.ReducedBuilding := M.metric
  let : CompleteSpace B.ReducedBuilding := M.complete
  let : IsIsometricSMul (rationalPoints G) B.ReducedBuilding := M.isometric
  have hNPC := M.nonpositivelyCurved
  have hgeo := Langlands.Geometry.Metric.KP.completeNPCGeodesic B.ReducedBuilding hNPC
  let x := B.apartmentMap (Classical.arbitrary B.Apartment)
  let O := (fun g : rationalPoints G => g • x) '' (H : Set (rationalPoints G))
  have hO : O.Nonempty := ⟨x, 1, H.one_mem, one_smul _ _⟩
  have hbounded : Bornology.IsBounded O :=
    (hH.image (M.continuous_orbit x)).isBounded
  obtain ⟨y, hy⟩ := Langlands.Geometry.Metric.KP.boundedSetStabilizerFixedPoint
    B.ReducedBuilding hNPC hgeo O hO hbounded
  refine ⟨y, fun h hh => hy (IsometryEquiv.constSMul h) ?_⟩
  change (fun z : B.ReducedBuilding => h • z) '' O = O
  ext z
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨h * g, H.mul_mem hh hg, mul_smul h g x⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(h⁻¹ * g) • x, ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) hg, rfl⟩, ?_⟩
    change h • (h⁻¹ * g) • x = g • x
    rw [smul_smul, mul_inv_cancel_left]

set_option maxHeartbeats 1000000 in
private theorem available_compact_open_maximal
    (D : KPBuildingDatum G) (hD : D.SatisfiesGroupAxioms)
    {y : D.base.ReducedBuilding} (hy : D.base.IsSpecialPoint y) :
    SpecialCompact.IsCompactOpenMaximal F (D.base.compactStabilizer y) := by
  let B := D.base
  have hA := hD.affineRootSystem.apartmentAxioms
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨hopen, hbound⟩ := hD.boundedSubgroups y
  have hclosed : IsClosed (B.compactStabilizer y : Set (rationalPoints G)) :=
    (B.compactStabilizer y).isClosed_of_isOpen hopen
  have hcompact : IsCompact (B.compactStabilizer y : Set (rationalPoints G)) := by
    exact (hbound.isCompact_closure G.X).of_isClosed_subset hclosed subset_closure
  obtain ⟨M⟩ := metricRealization F G B.isConnectedReductive B D.realization D.splitting
    hD.building hD.boundedSubgroups hD.affineStructure hD.affineRootSystem.rootReflections
    hA hD.affineRootSystem.compatibleApartmentFacets hD.titsSystem
  refine ⟨hcompact, hopen, hcompact, ?_⟩
  intro H hH hle
  obtain ⟨z, hz⟩ := compact_subgroup_fixes B M H hH
  have hF := rootRankOneFactorization F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hE : RelativeRoot.HasOppositeFactorPairs B.i :=
    fun a ha g hg hg1 => (hF a ha g hg hg1).1.exists
  have hzy : z = y := B.toValuationBuildingData.eq_of_compactStabilizer_fixed_of_special_buildingPoint
    hA hE hD.affineRootSystem.compatibleApartmentFacets.injective
    (fun x => D.realization.hasCommonApartmentWith_of_isBuilding hD.building.isBuilding
      (B.apartmentMap x)) hy (fun g hg => hz g (hle hg))
  have hnorm : H ≤ rationalCommonNormKernel G := compactSubgroup_le_rationalCommonNormKernel G H hH
  intro g hg
  exact B.mem_compactStabilizer.mpr ⟨hnorm hg, by simpa only [hzy] using hz g hg⟩

end Topology

section Core
open Langlands.AlgebraicGeometry.PointTopology
local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- Compact-open maximality implies bounded-open maximality for the same subgroup. -/
theorem isBoundedOpenMaximal_of_isCompactOpenMaximal
    (hG : IsConnectedReductive G) {K : Subgroup (rationalPoints G)}
    (hK : IsCompactOpenMaximal F K) : IsBoundedOpenMaximal F K := by
  let : Smooth G.X.hom := hG.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hbounded := Langlands.AlgebraicGeometry.PointTopology.isAlgebraicallyBounded_of_isCompact hK.1
  refine ⟨hbounded, hK.2.1, hbounded, ?_⟩
  intro H hH hKH
  have hcl : IsCompact (H.topologicalClosure : Set (rationalPoints G)) :=
    hH.isCompact_closure G.X
  exact H.le_topologicalClosure.trans (hK.2.2.2 hcl (hKH.trans H.le_topologicalClosure))

/-- The compact, bounded and Weyl clauses, without the still separate
standard-parabolic intersection identity. -/
theorem availableCompactCore (D : KPBuildingDatum G) (hD : D.SatisfiesGroupAxioms)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν)
    (x : D.base.Apartment) (hx : D.base.apartment.IsSpecialApartmentVertex x) :
    IsBoundedOpenMaximal F (D.base.apartment.specialCompactSubgroup x) ∧
      IsCompactOpenMaximal F (D.base.apartment.specialCompactSubgroup x) ∧
      HasWeylRepresentatives D.base.i (D.base.apartment.specialCompactSubgroup x) := by
  have hcompact := available_compact_open_maximal D hD
    (D.base.apartment.isSpecialBuildingPoint_apartmentMap hx.1)
  refine ⟨isBoundedOpenMaximal_of_isCompactOpenMaximal D.base.isConnectedReductive hcompact,
    hcompact, ?_⟩
  have hA := hD.affineRootSystem.apartmentAxioms
  have hF := rootRankOneFactorization F G D.base.isConnectedReductive D.base.S D.base.i
    D.base.isMaximalSplitTorus
  intro w
  obtain ⟨n, hn, hnw⟩ := WeylRepresentatives.special_parahoric_normalizer_surjective D.base hA
    hD.rootGroupAction.zeroFixerGenerators hF ν hν hx.1 w
  exact ⟨n, D.base.parahoricAt_le_compactStabilizer hA.topologyCompatible x hn, hnw⟩

/-- The same geometric compact has an identity basis normal in it whose
literal intersections form identity bases in every actual standard Levi. -/
theorem availableNormalBasisCore (D : KPBuildingDatum G) (hD : D.SatisfiesGroupAxioms)
    (x : D.base.Apartment) (hx : D.base.apartment.IsSpecialApartmentVertex x) :
    ∃ B : Set (Subgroup (rationalPoints G)),
      CompactOpenNormalBasis (D.base.apartment.specialCompactSubgroup x) B ∧
        ∀ (ν : cocharacterLattice D.base.S) (J : Set (characterLattice D.base.S)),
          InheritedCompactOpenNormalBasis (D.base.apartment.specialCompactSubgroup x)
            (standardLeviPoints D.base.i ν J) B := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let : TotallyDisconnectedSpace (rationalPoints G) :=
    rationalPoint_totallyDisconnectedSpace_of_localField F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have hcompact := available_compact_open_maximal D hD
    (D.base.apartment.isSpecialBuildingPoint_apartmentMap hx.1)
  obtain ⟨B, hB⟩ := exists_compactOpenNormalBasis
    (D.base.apartment.specialCompactSubgroup x) hcompact.1 hcompact.2.1
  refine ⟨B, hB, fun ν J => hB.inherited ?_⟩
  exact isClosed_rationalPoint_subgroup F (standardLevi D.base.i ν J)
    (Standard.leviHom D.base.i ν J) (Standard.isRepresentedBy_leviHom D.base.i ν J)
    (Standard.isClosedSubgroup_leviHom D.base.i ν J)

end Core
end Datum

end Langlands.BruhatTits.SpecialCompact
