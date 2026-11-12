import Langlands.Representation.CuspidalSupport.BernsteinData
import Langlands.Representation.Exponents.RepresentedCuspidalityComparison
import Langlands.Representation.Aubert.General.RationalLeviCuspidalityTransportProof
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Actual Bernstein cuspidal data are represented-supercuspidal -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinRepresentedCuspInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance bernsteinRepresentedCuspInstance2 : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
local instance bernsteinRepresentedCuspInstance3 : TopologicalSpace (rationalPoints G) := pointTopology
local instance bernsteinRepresentedCuspInstance4 (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance bernsteinRepresentedCuspInstance5 (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance bernsteinRepresentedCuspInstance6 (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

include family in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The actual represented standard parabolic, Levi and radical have the
geometric properties required by the represented-parabolic functors. -/
theorem bernsteinStandardRepresentativesGeometric (I : Finset (SimpleRoot i ν)) :
    IsParabolicSubgroup (Standard.parabolicHom i ν (rootSet i ν I)) ∧
      IsRationalLeviSubgroup (Standard.leviToParabolic i ν (rootSet i ν I)) ∧
      LeviSubgroup.IsGeometricUnipotentRadical
        (Standard.unipotentToParabolic i ν (rootSet i ν I)) ∧
      IsIso (subgroupMultiplication
        (Standard.leviToParabolic i ν (rootSet i ν I))
        (Standard.unipotentToParabolic i ν (rootSet i ν I))) :=
  RepresentedParabolic.standard_representatives_geometric_of_standardCocharacter
    i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
    family.genericCocharacter I

local instance bernsteinRepresentedCuspInstance7 (I : Finset (SimpleRoot i ν)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme i ν I)) := by
  have := (isClosed_levi i ν I).locallyCompactSpace
  exact (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance bernsteinRepresentedCuspInstance8 (I : Finset (SimpleRoot i ν)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme i ν I)) := by
  let e := leviRationalPointHomeomorph i ν I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme i ν I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

/-- The standard-Jacquet cuspidality in a Bernstein datum implies vanishing
for every proper actual represented parabolic of its actual rational Levi. -/
theorem BernsteinCuspidalDatum.isSupercuspidal
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    RepresentedParabolic.IsSupercuspidal a.representation := by
  classical
  let I := a.roots
  let : Mono i.hom.hom.left := family.maximalSplitTorus.isSplitSubtorus.mono
  let hgeom := bernsteinStandardRepresentativesGeometric i ν family I
  let hL := hgeom.2.1.isConnectedReductive
  let j := standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
  have hj : IsMaximalSplitTorus j :=
    family.maximalSplitTorus.isMaximalSplitTorus_standardLeviTorusFactor
      i ν (rootSet i ν I) (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have hjmono := hj.isSplitSubtorus.mono
  let : Mono j.hom.hom.left := hjmono
  have hνj : IsGenericCocharacter j ν :=
    (standardLeviStandardFamilies dynamicLie standardCocharacter F G
      family.connectedReductive T i family.maximalSplitTorus ν
      family.genericCocharacter (rootSet i ν I) (rootSet_subset i ν I)
      (bernsteinLeviScheme i ν I) hL (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  have hRoots := relativeRootSystem F (bernsteinLeviScheme i ν I) hL T j hj
  let := simpleRelativeRootFintype j hRoots hj.isSplitSubtorus.1 ν
  let hOwn := isSemidirectDecomposition_of_standardCocharacterStatement
    j ν standardCocharacter hL hj hνj
  have hUL (J : Finset (SimpleRoot j ν)) :
      IsClosed (unipotent j ν J : Set (rationalPoints (bernsteinLeviScheme i ν I))) :=
    isClosed_unipotent j ν J
  let A := bernsteinLiteralLeviRep i ν I a.representation
  have hc := (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
    F G family.connectedReductive T i family.maximalSplitTorus ν
    family.genericCocharacter I hL family.closedUnipotent hUL
    (family.closedLevi I) (family.leviDecomposition I) hOwn A).mpr a.cuspidal
  have hc' : IsCuspidal (parabolic j ν) (levi j ν) (unipotent j ν)
      hOwn hUL a.representation :=
    hc.of_iso (SmoothRep.pullbackSymmIso (leviRationalPointHomeomorph i ν I).symm
      a.representation).symm
  exact RepresentedParabolic.isSupercuspidal_of_isCuspidal j ν
    parabolicDynamic smoothMaximalSplitTorusConjugacy hL hj hνj hRoots
    hOwn hUL a.representation hc'

/-- The original actual representation, now certified irreducible and
supercuspidal for all proper represented parabolics of its actual Levi. -/
def BernsteinCuspidalDatum.representedSupercuspidal
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family) :
    {ρ : SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)) //
      ρ.IsIrreducible ∧ RepresentedParabolic.IsSupercuspidal ρ} :=
  ⟨a.representation, a.irreducible, a.isSupercuspidal i ν family⟩

end Langlands.CuspidalSupport
