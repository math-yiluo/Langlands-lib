import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitContinuity

/-! # Source-normalized Schwartz membership and continuity targets (VI.3.1) -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
open Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.RationalDynamicSource Langlands.Plancherel.RationalPlancherelDensity

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
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)

local instance standardLeviSchwartzAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviSchwartzAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviSchwartzFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviSchwartzTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviSchwartzNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
  rationalPoints_nonarchimedeanGroup 𝐋

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ 𝐋) (hs : IsSplitComponent s)
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs

-- Both instances follow from centrality; explicit binders make typeclass synthesis inferable.
variable [(CM).Normal] [(rationalPoints.map s).range.Normal]

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)

set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit CM hCM mu νM (discreteSeriesClass CM hCM mu π hsq)

variable
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

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ
  p qrev hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

variable (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

set_option hygiene false in
local notation "W" => standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
  Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
  hD hne hirr hreg
set_option hygiene false in
local notation "rhoX" => standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex
set_option hygiene false in
local notation "omegaπ" => discreteSeriesClass CM hCM mu π hsq
set_option hygiene false in
local notation "dO" => discreteSeriesOrbitMeasure νM CM hCM mu omegaπ rhoX
set_option hygiene false in
local notation "packet" => standardLeviPlancherelWavePacket hG hi hν I hζ π CM hCM mu hsq
  hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
  hneReverse hDReverseΩ hD hne hirr hreg hKc hPK rhoX

/-- The first conclusion of VI.3.1 at the I.1 character scale: every smooth section has an
integrable actual weighted coefficient at every point and its packet is fully Schwartz. -/
def StandardLeviPlancherelWavePacketMembershipStatement : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  ∀ q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
    (∀ g : rationalPoints G,
      Integrable (fun omega : Oπ => W omega *
        rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π CM hCM mu hsq q omega g) dO) ∧
    packet q ∈ schwartzSubmodule (rationalXi hKc hPK) (rationalHeight (F := F) ρ)

/-- The second conclusion of VI.3.1: synthesis into the existing Schwartz topology is a
continuous complex-linear map whose values are the same I.1-normalized actual orbit integral.
No Schwartz-valued lift or estimate is an input. -/
def StandardLeviPlancherelWavePacketContinuityStatement : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  letI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  ∃ synth : rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π →L[ℂ]
      RationalSchwartzSpace hKc hPK ρ,
    ∀ (q : rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π) (g : rationalPoints G),
      synth q g = ∫ omega : Oπ, W omega *
        rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π CM hCM mu hsq
          (OrbitSectionSpace.toSections (G := rationalPoints G)
            (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) νM π
            (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
            (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K
            (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
            (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
            (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
            (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) q)
          omega g ∂dO

/-- The joint principal target, explicitly at the transported I.1 character scale and with
square integrability modulo the actual split component on the literal standard Levi. -/
def StandardLeviPlancherelWavePacketSourceNormalizedStatement : Prop :=
  StandardLeviPlancherelWavePacketMembershipStatement hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ ∧
  StandardLeviPlancherelWavePacketContinuityStatement hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ

end Langlands.HarishChandraSchwartz
