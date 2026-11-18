import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.GroupScheme.SimplyConnected.CoverPreimageToolkit

/-! # Transporting a finite Cartan cover to the intrinsic standard Levi -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

local instance cartanLeviTransportAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance cartanLeviTransportFiniteType :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom := leviScheme_locallyOfFiniteType i ν J
local instance cartanLeviTransportAffine : IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The intrinsic torus centralizer is the exact preimage of the ambient
centralizer under the standard-Levi point embedding. -/
theorem mem_centralizerPoints_leviScheme (x : rationalPoints (Standard.leviScheme i ν J)) :
    x ∈ centralizerPoints (Standard.leviTorusHom i ν J) ↔
      rationalPoints.map (Standard.leviHom i ν J) x ∈ centralizerPoints i := by
  have : Mono (Standard.leviHom i ν J).hom.hom :=
    (Standard.isRepresentedBy_leviHom i ν J).1
  have h := torusCentralizer_comp_comap_of_mono (Standard.leviTorusHom i ν J)
    (Standard.leviHom i ν J)
  rw [Standard.leviTorusHom_comp] at h
  rw [← torusCentralizer_carrier_base, ← torusCentralizer_carrier_base, ← h]
  rfl

/-- Lift an ambient torus-centralizer point to the intrinsic standard Levi,
using its canonical point homeomorphism. -/
def leviSchemeCentralizerPointLift (z : centralizerPoints i) :
    centralizerPoints (Standard.leviTorusHom i ν J) :=
  ⟨(leviSchemePointsEquiv i ν J).symm
      ⟨z.val, centralizerPoints_le_standardLeviPoints i ν J z.property⟩,
    (mem_centralizerPoints_leviScheme i ν J _).mpr (by
      rw [map_leviSchemePointsEquiv_symm]
      exact z.property)⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem map_leviSchemeCentralizerPointLift (z : centralizerPoints i) :
    rationalPoints.map (Standard.leviHom i ν J) (leviSchemeCentralizerPointLift i ν J z).val =
      z.val :=
  map_leviSchemePointsEquiv_symm i ν J _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The intrinsic Levi has precisely the selected ambient simple roots. -/
theorem simpleRelativeRoots_leviScheme (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    simpleRelativeRoots (Standard.leviTorusHom i ν J) ν = J := by
  have hL := Langlands.BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hG i hi ν hν J hJ
  exact (standardLeviStandardFamilies dynamicLie standardCocharacter F G hG S i hi ν hν J hJ
    (Standard.leviScheme i ν J) hL (Standard.leviHom i ν J)
    (Standard.isRepresentedBy_leviHom i ν J) (Standard.isClosedSubgroup_leviHom i ν J)).1

omit [LocallyOfFiniteType G.X.hom] in
/-- A literal standard-Levi Cartan cover is a finite Cartan cover for its
representing group scheme at the exact inherited compact subgroup. -/
theorem finiteCartanCovering_leviScheme (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    {K0 : Subgroup (rationalPoints G)}
    (hcover : StandardLeviCartanCovering F i ν J K0) :
    Langlands.Aubert.General.RationalPointFamily.FiniteCartanCovering F
      (Standard.leviTorusHom i ν J) ν (leviSchemeCompact K0 i ν J) := by
  classical
  obtain ⟨F0, hF0⟩ := hcover
  refine ⟨F0.image (leviSchemeCentralizerPointLift i ν J), fun g => ?_⟩
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hg⟩ :=
    hF0 (leviSchemePointsEquiv i ν J g).val (leviSchemePointsEquiv i ν J g).property
  let k₁L := (leviSchemePointsEquiv i ν J).symm ⟨k₁, hk₁.2⟩
  let k₂L := (leviSchemePointsEquiv i ν J).symm ⟨k₂, hk₂.2⟩
  refine ⟨k₁L, k₂L, leviSchemeCentralizerPointLift i ν J f, a, ?_, ?_,
    Finset.mem_image.mpr ⟨f, hf, rfl⟩, ?_, ?_⟩
  · change rationalPoints.map (Standard.leviHom i ν J) k₁L ∈ K0
    dsimp only [k₁L]
    rw [map_leviSchemePointsEquiv_symm]
    exact hk₁.1
  · change rationalPoints.map (Standard.leviHom i ν J) k₂L ∈ K0
    dsimp only [k₂L]
    rw [map_leviSchemePointsEquiv_symm]
    exact hk₂.1
  · rw [simpleRelativeRoots_leviScheme i ν J hG hi hν hJ]
    exact ha
  · apply map_leviHom_injective
    have htorus : rationalPoints.map (Standard.leviHom i ν J)
        (rationalPoints.map (Standard.leviTorusHom i ν J) a) = rationalPoints.map i a := by
      rw [← Langlands.Aubert.General.RationalPointFamily.rationalPoints_map_comp_apply,
        Standard.leviTorusHom_comp]
    simpa only [map_mul, k₁L, k₂L, map_leviSchemePointsEquiv_symm,
      map_leviSchemeCentralizerPointLift, htorus, leviSchemePointsEquiv_coe] using hg

end Langlands.HarishChandraSchwartz
