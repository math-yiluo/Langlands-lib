import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPacketRankAssembly
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLowerPacketOpenFullDomains

/-! # Proper-face expansion data for the standard-Levi induction -/

noncomputable section

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.DynamicOppositeStandardIntertwining

namespace Langlands.HarishChandraSchwartz

open RationalPointFamily WeakExpansion

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  LowerPacket.lowerPacketLeviAffineHom LowerPacket.lowerPacketLeviFiniteType

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance properFaceAssemblyLeviAffine {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

local instance properFaceAssemblyLeviTopology {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S)) :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν J)) :=
  rationalPointTopology F (Standard.leviScheme i ν J).X

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
  [(CM).Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (P : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG Aπ)
  {L : OpenSubgroup (rationalPoints G)} (hLc : IsCompact (L : Set (rationalPoints G)))
  (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) L.toSubgroup)

set_option hygiene false in
local notation "PG" => upperDensityAtPacketCompact hG hi hν I hζ hLc hPL π hRefl hCST P

set_option hygiene false in
local notation "index[" J "]" => WeylIndex i ν (rootSet i ν I) (rootSet i ν J)

set_option maxHeartbeats 2000000 in
/-- At a common special compact, open full convergence domains and the exact
weighted pointwise expansion supply the proper-face induction data. -/
def StandardLeviPacketProperFaceAssemblyStatement : Prop :=
  IsSpecialVertexCompact ν hi L →
    (∀ (I' : Finset (SimpleRoot i ν))
      (R : Representatives i ν (rootSet i ν I) (rootSet i ν I')),
      (∃ α : SimpleRoot i ν, α ∉ I') → LiftsInCompact I I' (K := L) R →
      rootSet i ν I' ≠ ∅ → ∀ w : index[I'],
        LowerPacketOpenFullDomains hG hi hν I I' hζ (R.normalizer w) (R.levi_le w) π hLc) →
    (∀ (I' : Finset (SimpleRoot i ν)) {ζ' : cocharacterLattice S}
      (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
      {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
      (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
      (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
      (PM : ∀ w : index[I'],
        LowerDensityPackage hG hi hν I I' hζ (R.normalizer w) (R.levi_le w) π hRefl hCST),
      WeightedWeakExpansionStatement hG hi hν I I' hζ hζ' hLc hPL s hs π mu hsq
        hRefl hCST PG hA R PM) →
    StandardLeviPacketProperFaceExpansionAt hG hi hν I hζ s hs π mu hsq hRefl hCST P hLc hPL

set_option maxHeartbeats 4000000 in
/-- Construct the proper-face induction data with the original literal compact intersections. -/
theorem standardLeviPacketProperFaceExpansionAt_of_openFullDomains :
    StandardLeviPacketProperFaceAssemblyStatement hG hi hν I hζ s hs π mu hsq hRefl hCST P hLc hPL := by
  classical
  intro hspecial hDomains hPointwise I' ζ' hζ' A qA hA R hproper hlifts
  have hFactors := standardLeviDynamicIwasawaAt_of_minimal i ν L.toSubgroup hG hi hν
    (standardLeviIwasawaFactorsAt_and_weylRepresentatives_of_special hG hi hν hspecial hPL).1
  have hPackages (w : index[I']) :
      ∃ PM : LowerDensityPackage hG hi hν I I' hζ (R.normalizer w) (R.levi_le w) π hRefl hCST,
      PM.K.toSubgroup = leviSchemeCompact L.toSubgroup i ν (rootSet i ν I') := by
    have hFull : LowerPacketOpenFullDomains hG hi hν I I' hζ (R.normalizer w) (R.levi_le w) π hLc := by
      by_cases hEmpty : rootSet i ν I' = ∅
      · exact lowerPacketOpenFullDomains_of_emptyOutput hG hi hν I I' hζ
          (R.normalizer w) (R.levi_le w) π hLc hEmpty
      · exact hDomains I' R hproper hlifts hEmpty w
    exact exists_lowerDensityPackage_at_compact_of_openFullDomains hG hi hν I I' hζ
      (R.normalizer w) (R.levi_le w) π hLc s hs mu hsq hRefl hCST hFactors hFull
  choose PM hPM using hPackages
  exact ⟨PM, hPM, hPointwise I' hζ' hA R PM⟩

end Langlands.HarishChandraSchwartz
