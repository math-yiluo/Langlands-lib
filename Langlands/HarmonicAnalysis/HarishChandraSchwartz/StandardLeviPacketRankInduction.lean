import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviLowerPacketBound
import Langlands.GroupScheme.Rational.StandardLeviNestedTransport

/-! # Specializing the VI.3.1 induction hypothesis to strict lower rank -/

noncomputable section

set_option maxRecDepth 10000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.RationalDynamicSource Langlands.Plancherel.RationalPlancherelDensity
open RationalPointFamily

namespace Langlands.HarishChandraSchwartz

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

section ExactFamily

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

attribute [local instance] LowerPacket.lowerPacketLeviAffineHom LowerPacket.lowerPacketLeviFiniteType

local instance rankLeviAffine {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom

local instance rankLeviTopology {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T)) :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν J)) :=
  rationalPointTopology F (Standard.leviScheme i ν J).X

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
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
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ
  p qrev hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

set_option maxHeartbeats 2500000 in
/-- The exact joint VI.3.1 target for all ambient groups and maximal split tori of
relative root rank `r` over the fixed local field. All inducing and packet data vary. -/
def StandardLeviPlancherelWavePacketAtRankStatement (r : ℕ) : Prop :=
  ∀ {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : T.toGrp ⟶ G} {ν : cocharacterLattice T},
    relativeRootRank i = r →
    ∀ (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
      (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
      {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
      {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
      (s : A.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
      (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
      [(CM).Normal] [(rationalPoints.map s).range.Normal]
      (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
      [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
      (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
      (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
      (hRefl : RelativeRootReflectionExistenceStatement.{u})
      (hCST : CentralSplitTorusCharacterStatement.{u})
      (Ks : OpenSubgroup (RationalPoint F G.X))
      (hKs : IsCompact (Ks : Set (RationalPoint F G.X)))
      (hPKs : ∀ g : RationalPoint F G.X,
        ∃ p : parabolic χ, ∃ k : Ks, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
      (hOppKs : ∀ g : RationalPoint F G.X,
        ∃ p : oppositeParabolic χ, ∃ k : Ks,
          g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
      (p : ForwardContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
      (qrev : ReverseContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
      {DForward DReverse : Set (unramifiedCharacters νL)}
      (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
      (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ Ks hKs Aπ)
      (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
      (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ Ks hKs Aπ)
      {D : Set (unramifiedCharacters νL)}
      (hD : IsOpen D) (hne : D.Nonempty)
      (hirr : ∀ z ∈ D,
        (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
          (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)
      (hreg : RationalFunctionUnitaryRegular (parameterScheme χ) (parameterScheme_isConnectedReductive χ hG)
        (jP)⁻¹)
      {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
      {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)),
      StandardLeviPlancherelWavePacketSourceNormalizedStatement hG hi hν I hζ s hs hindex π mu hsq
        hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
        hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ

end ExactFamily

namespace LowerPacket

open WeakExpansion LowerChamber LowerSplitCenter

attribute [local instance] lowerPacketLeviAffineHom lowerPacketLeviFiniteType

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
  (hi : IsMaximalSplitTorus i) (I' : Finset (SimpleRoot i ν)) (ζ : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hν : IsGenericCocharacter i ν)
  (I : Finset (SimpleRoot i ν)) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)

set_option hygiene false in
local notation "M'" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "iL" => Standard.leviTorusHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left] (s : A.toGrp ⟶ 𝐋)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s

variable [(CM).Normal] [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure] (hs : IsSplitComponent s)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (hsq : IsSquareIntegrableModCentralSubgroup CM (rationalLeviSplitCenter_le_center I s hs)
    π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "Index" => WeylIndex i ν (rootSet i ν I) (rootSet i ν I')
set_option hygiene false in
local notation "cutLevi" => standardLeviPoints i ν (rootSet i ν I')
set_option hygiene false in
local notation "wN[" w "]" => R.normalizer w
set_option hygiene false in
local notation "wL[" w "]" => R.levi_le w
set_option hygiene false in
local notation "cₛ[" w "]" => lowerChamber hi I' ζ wN[w]
set_option hygiene false in
local notation "sₛ[" w "]" => lowerSplit hi I' ζ wN[w] hG hν I hζ wL[w] s
set_option hygiene false in
local notation "Qₛ[" w "]" =>
  (standardLeviPoints iL (cₛ[w]).chamber (rootSet iL (cₛ[w]).chamber (cₛ[w]).labels)) ⧸
    rationalLeviSplitCenter (cₛ[w]).labels sₛ[w]
set_option hygiene false in
local notation "ρM" => ρ.restrict (Standard.leviHom i ν (rootSet i ν I'))

set_option maxHeartbeats 10000000 in
/-- On a proper output face, the exact joint packet theorem at every smaller relative rank
provides the lower continuity inputs to the weak constant-term bound. -/
theorem lowerDynamicPacketChamberEstimates_of_rankIH [(rationalPoints.map s).range.Normal]
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
    (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf cutLevi)
      (K.toSubgroup.subgroupOf cutLevi))
    (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
      (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
    (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
    (PM : ∀ w : Index, LowerDensityPackage hG hi hν I I' hζ wN[w] wL[w] π hRefl hCST)
    (hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM)
    {D : ℕ} [Nonempty (Fin D)] (ρ : MatrixRepresentation G (Fin D))
    (hproper : ∃ a : SimpleRoot i ν, a ∉ I')
    (hIH : ∀ r < relativeRootRank i,
      StandardLeviPlancherelWavePacketAtRankStatement.{u,uV} (F := F) r) :
    LowerDynamicPacketChamberEstimates hG hi hν I I' hζ hKc s hs hindex π mu hsq hRefl hCST
      R PM hMK ρ := by
  have hlt := StandardLeviNested.relativeRootRank_leviTorusHom_rootSet_lt hG i hi ν hν I' hproper
  apply lowerDynamicPacketChamberEstimates_of_continuity hi I' ζ hG hν I hζ s mu hs π hsq
    hRefl hCST hindex hKc hMK PG R PM hN ρ
  intro w hPK'
  have := lowerSplitCenter_normal hi I' ζ wN[w] hG hν I hζ wL[w] s hs
  have := lowerSplit_range_normal hi I' ζ wN[w] hG hν I hζ wL[w] s hs
  let : MeasurableSpace Qₛ[w] := borel _
  have : BorelSpace Qₛ[w] := ⟨rfl⟩
  let P := lowerChamberPackage hi I' ζ wN[w] hG hν I hζ wL[w] π hRefl hCST (PM w)
  have hsmall : StandardLeviPlancherelWavePacketAtRankStatement.{u,uV} (F := F)
      (relativeRootRank iL) := hIH (relativeRootRank iL) hlt
  have ht := hsmall (i := iL) (ν := (cₛ[w]).chamber) rfl
    (lowerAmbient_isConnectedReductive hG hi hν I') (lowerTorus_isMaximalSplitTorus hi I')
    (cₛ[w]).isGeneric (cₛ[w]).labels (cₛ[w]).isStandard sₛ[w]
    (isSplitComponent_lowerSplit hi I' ζ wN[w] hG hν I hζ wL[w] s hs)
    (finiteIndex_lowerSplit hi I' ζ wN[w] hG hν I hζ wL[w] s hs)
    (lowerChamberRepresentation hi I' ζ wN[w] hG hν I hζ wL[w] π)
    (lowerChamberQuotientMeasure hi I' ζ wN[w] hG hν I hζ wL[w] s mu)
    (lowerChamberRepresentation_isSquareIntegrable hi I' ζ wN[w] hG hν I hζ wL[w] s mu hs π hsq)
    hRefl hCST P.K P.hK P.hPK P.hOppK P.p P.q P.hDForward P.hneForward P.hDForwardΩ
    P.hDReverse P.hneReverse P.hDReverseΩ P.hD P.hne P.hirr P.hreg
    (lowerK_isCompact hG hi hν I I' hζ wN[w] wL[w] hRefl hCST π (PM w)) hPK' ρM
  exact ht.2

end LowerPacket

end Langlands.HarishChandraSchwartz
