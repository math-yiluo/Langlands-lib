import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketRegularity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionSchwartzSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacketLevelInvariance

/-! # Internal fixed-level reduction for the source-normalized packet -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

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

local instance standardLeviPacketEstimateSynthesisAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketEstimateSynthesisAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketEstimateSynthesisFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketEstimateSynthesisTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketEstimateSynthesisNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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


set_option hygiene false in
local notation "decomp" => isSemidirectDecomposition_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I)
set_option hygiene false in
local notation "closedU" => isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)
set_option hygiene false in
local notation "closedP" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "normContinuous" => RationalPointFamily.continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "projectionContinuous" => continuous_projection_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I) _
set_option hygiene false in
local notation "factorization" =>
  factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "coordinates" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel νM π coordinates decomp closedU K closedP
  hKc normContinuous projectionContinuous factorization
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections νM π coordinates decomp closedU K
  closedP hKc normContinuous projectionContinuous factorization
set_option hygiene false in
local notation "sectionIdentity" => OrbitSectionSpace.toSections νM π coordinates decomp closedU K
  closedP hKc normContinuous projectionContinuous factorization
set_option hygiene false in
local notation "synthL" => standardLeviPlancherelWavePacketLinear hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ∘ₗ sectionIdentity

/-- The source-normalized packet preserves the same subgroup that fixes the input section. -/
theorem standardLeviPlancherelWavePacket_biInvariant_of_level :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (H : OpenSubgroup (rationalPoints G)) (q : SectionLevel H),
      IsBiInvariant H (packet (includeLevel H q)) := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  intro H q
  exact inducedOrbitWavePacket_biInvariant_of_level decomp closedU closedP K hKc factorization
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    νM π normContinuous projectionContinuous coordinates CM hCM mu hsq rhoX W H q

/-- Internal analytic obligation: finite derivative bounds for the actual source-normalized
packet, with the original rational Xi and full matrix height. -/
def StandardLeviPacketDerivativeEstimates : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  OrbitSectionSchwartzEstimates νM π coordinates decomp closedU K closedP hKc
    normContinuous projectionContinuous factorization (rationalXi hKc hPK)
    (rationalHeight (F := F) ρ) synthL

/-- Internal conditional synthesis; the derivative estimates are still an obligation. -/
def standardLeviPacketSchwartzFromEstimates
    (hest : StandardLeviPacketDerivativeEstimates hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ) :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π →L[ℂ] RationalSchwartzSpace hKc hPK ρ := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  exact OrbitSectionSchwartzSynthesis.continuousLinear νM π coordinates decomp closedU K
    closedP hKc normContinuous projectionContinuous factorization (rationalXi hKc hPK)
    (rationalHeight (F := F) ρ) synthL
    (fun H q => standardLeviPlancherelWavePacket_biInvariant_of_level hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK H.1 q) hest

/-- The conditional synthesis retains the original actual packet pointwise. -/
theorem standardLeviPacketSchwartzFromEstimates_apply
    (hest : StandardLeviPacketDerivativeEstimates hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ) :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (q : rationalInducedOrbitSectionSpace hG hi hν I hKc hPK π) (g : rationalPoints G),
      standardLeviPacketSchwartzFromEstimates hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ hest q g =
        packet (sectionIdentity q) g := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  intro q g
  rfl

/-- Internal reduction only: once the actual derivative estimates are proved, the original
joint target follows with no further analytic inputs. -/
theorem standardLeviPlancherelWavePacketSourceNormalized_of_estimates
    (hest : StandardLeviPacketDerivativeEstimates hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ) :
    StandardLeviPlancherelWavePacketSourceNormalizedStatement hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let synth := standardLeviPacketSchwartzFromEstimates hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ hest
  constructor
  · intro q
    refine ⟨integrable_standardLeviPlancherelWavePacket_integrand hG hi hν I hζ s hs hindex π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK q, ?_⟩
    exact (synth q).property
  · exact ⟨synth, fun q g => rfl⟩

end Langlands.HarishChandraSchwartz
