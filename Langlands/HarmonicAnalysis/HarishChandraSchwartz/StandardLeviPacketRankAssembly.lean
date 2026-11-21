import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPacketSpecialAssembly
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviWeightedWeakTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPacketRankInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviRankZeroPacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakPacketIdentityProof

/-! # Rank induction for source-normalized standard-Levi packets -/

noncomputable section

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.Geometry.Building
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.RationalDynamicSource

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

local instance rankAssemblyLeviAffine {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

local instance rankAssemblyLeviTopology {S : CommGroupScheme (Spec (CommRingCat.of F))}
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

section AtCompact

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
  [(CM).Normal] [(rationalPoints.map s).range.Normal]
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

set_option maxHeartbeats 2000000 in
/-- The lower density packages at the literal compact intersection and the
pointwise weighted expansion for those packages on each proper face. -/
def StandardLeviPacketProperFaceExpansionAt : Prop :=
  ∀ (I' : Finset (SimpleRoot i ν)) {ζ' : cocharacterLattice S}
    (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
    (R : Representatives i ν (rootSet i ν I) (rootSet i ν I')),
    (∃ α : SimpleRoot i ν, α ∉ I') → LiftsInCompact I I' (K := L) R →
    ∃ PM : ∀ w : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
        LowerDensityPackage hG hi hν I I' hζ (R.normalizer w) (R.levi_le w) π hRefl hCST,
      (∀ w, (PM w).K.toSubgroup = leviSchemeCompact L.toSubgroup i ν (rootSet i ν I')) ∧
      WeightedWeakExpansionStatement hG hi hν I I' hζ hζ' hLc hPL s hs π mu hsq
        hRefl hCST PG hA R PM

set_option maxHeartbeats 6000000 in
/-- The lower-rank continuity theorem bounds the weak term when the actual
lower packages and pointwise expansion are available at the special compact. -/
theorem standardLeviPacketWeakBoundsAt_of_rankIH
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hspecial : IsSpecialVertexCompact ν hi L)
    (hbasis : SimultaneousStandardBasisAt i ν L.toSubgroup)
    (hcover : StandardLeviCartanCovering F i ν ∅ L.toSubgroup)
    (hFactors : StandardLeviIwasawaFactorsAt (i := i) (ν := ν) L.toSubgroup)
    (hWeyl : HasWeylRepresentatives i L.toSubgroup)
    (hexpansion : StandardLeviPacketProperFaceExpansionAt hG hi hν I hζ s hs π mu hsq
      hRefl hCST P hLc hPL)
    (hIH : ∀ rank < relativeRootRank i,
      StandardLeviPlancherelWavePacketAtRankStatement.{u,uV} (F := F) rank) :
    StandardLeviPacketWeakBoundsAt hG hi hν I hζ s hs hindex π mu hsq hRefl hCST
      P.K P.hK P.hPK P.hOppK P.p P.q P.hDForward P.hneForward P.hDForwardΩ
      P.hDReverse P.hneReverse P.hDReverseΩ P.hD P.hne P.hirr P.hreg ρ hLc hPL := by
  classical
  intro I' hI' A qA hA
  have hproper : ∃ α : SimpleRoot i ν, α ∉ I' := by
    obtain ⟨α, hsimple, hmissing⟩ := Set.exists_of_ssubset hI'
    exact ⟨⟨α, hsimple⟩, fun hmem => hmissing ((val_mem_rootSet i ν I' ⟨α, hsimple⟩).2 hmem)⟩
  obtain ⟨ζ', hζ'⟩ := exists_standardCocharacter_of_relativeRootReflectionExistenceStatement
    hRefl F G hG S i hi ν hν (rootSet i ν I') (rootSet_subset i ν I')
  obtain ⟨R, hlifts⟩ := exists_representatives_liftsInCompact hG hi hν I I' hWeyl
  obtain ⟨PM, hlowerK, hpointwise⟩ := hexpansion I' hζ' hA R hproper hlifts
  have hNorm : SourceCompactNormalization hG hi hν I I' hζ (K := L) π hRefl hCST PG R PM :=
    fun w => ⟨rfl, hlowerK w⟩
  have hPacket := weightedPacketIdentity_of_weightedWeakExpansion hG hi hν I I' hζ hζ' hLc hPL
    s hs hindex π mu hsq hRefl hCST PG hA R PM hpointwise
  have hMK := hFactors (rootSet i ν I') (rootSet_subset i ν I')
  have hlower := LowerPacket.lowerDynamicPacketChamberEstimates_of_rankIH hi I' ζ hG hν I hζ
    s mu hs π hsq hRefl hCST hindex hLc hMK PG R PM hNorm ρ hproper hIH
  exact rationalOrbitLevelWeakPacketRapid_of_commonCompact_lowerEstimates hG hi hν I hζ
    hLc hPL π hRefl hCST P s hs hindex mu hsq I' hζ' hA R PM hMK ρ
    hproper hspecial hlifts hlowerK hpointwise hPacket hbasis hcover hlower

end AtCompact

set_option maxHeartbeats 2000000 in
/-- The proper-face input at any common special compact over the given field. -/
def StandardLeviPacketProperFaceExpansionStatement : Prop :=
  ∀ {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
    {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
    (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
    [(CM).Normal] [(rationalPoints.map s).range.Normal]
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
    (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (P : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG Aπ)
    (L : OpenSubgroup (rationalPoints G)) (hLc : IsCompact (L : Set (rationalPoints G)))
    (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) L.toSubgroup),
    IsSpecialVertexCompact ν hi L →
    StandardLeviPacketProperFaceExpansionAt hG hi hν I hζ s hs π mu hsq hRefl hCST P hLc hPL

/-- The joint packet conclusion at every rank follows from Bruhat–Tits
availability and the proper-face expansion at common special compacts. -/
def StandardLeviPacketRankReductionStatement : Prop :=
  BruhatTitsAvailabilityStatement.{u} →
    StandardLeviPacketProperFaceExpansionStatement.{u,uV} (F := F) →
    ∀ rank, StandardLeviPlancherelWavePacketAtRankStatement.{u,uV} (F := F) rank

set_option maxHeartbeats 6000000 in
/-- Strong rank induction for the published joint packet conclusion, given
Bruhat–Tits availability and the proper-face expansion with lower densities. -/
theorem standardLeviPlancherelWavePacketAtRank_of_properFaceExpansion :
    StandardLeviPacketRankReductionStatement.{u,uV} (F := F) := by
  intro hAvail hexpansion rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
    intro S G _ _ i ν hRank hG hi hν I ζ hζ T _ s hs hindex _ _ π _ _ mu _ hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev DForward DReverse hDForward hneForward hDForwardΩ
      hDReverse hneReverse hDReverseΩ D hD hne hirr hreg K hKc hPK n _ ρ
    by_cases hzero : relativeRootRank i = 0
    · exact standardLeviPlancherelWavePacketRankZero hG hi hν I hζ s hs hindex π mu hsq
        hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
        hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ hzero
    · let P : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG Aπ := {
        K := Ks
        hK := hKs
        hPK := hPKs
        hOppK := hOppKs
        p := p
        q := qrev
        DForward := DForward
        DReverse := DReverse
        hDForward := hDForward
        hneForward := hneForward
        hDForwardΩ := hDForwardΩ
        hDReverse := hDReverse
        hneReverse := hneReverse
        hDReverseΩ := hDReverseΩ
        D := D
        hD := hD
        hne := hne
        hirr := hirr
        hreg := hreg }
      apply standardLeviPlancherelWavePacketSourceNormalized_of_specialCompact_weakBounds
        hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
        hKc hPK ρ (hasSpecialPacketCompact_of_availability hi ν hAvail hG hν)
      intro L hLc hPL hspecial hbasis hcover hFactors hWeyl
      exact standardLeviPacketWeakBoundsAt_of_rankIH hG hi hν I hζ s hs π mu hsq hRefl hCST
        P hLc hPL hindex ρ hspecial hbasis hcover hFactors hWeyl
        (hexpansion hG hi hν I hζ s hs π mu hsq hRefl hCST P L hLc hPL hspecial)
        (fun smaller hlt => ih smaller (hlt.trans_le hRank.le))

end Langlands.HarishChandraSchwartz
