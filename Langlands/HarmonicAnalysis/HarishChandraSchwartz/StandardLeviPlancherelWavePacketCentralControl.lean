import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketRegularity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionLevelCentralDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviSquareIntegrableCoefficientBound

/-! # Central Fourier control for the source-normalized standard-Levi packet -/

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

local instance standardLeviPacketCentralControlAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCentralControlAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketCentralControlFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketCentralControlTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketCentralControlNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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
local notation "rootsI" => RationalPointFamily.rootSet i ν I
set_option hygiene false in
local notation "iL" => Standard.leviTorusHom i ν rootsI

variable (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν rootsI))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν rootsI)))
  {K0L : Subgroup (rationalPoints 𝐋)}
  (hK0Lc : IsCompact (K0L : Set (rationalPoints 𝐋)))
  (hbasis : Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisAt iL ν K0L)
  (hcover : RationalPointFamily.FiniteCartanCovering F iL ν K0L)

set_option hygiene false in
local notation "coefficientXiBound" =>
  hasXiBoundedCoefficients_standardLeviSquareIntegrable hG hi hν I s hs hindex π mu hsq
    hKc hMK hK0Lc hbasis hcover ρ

set_option hygiene false in
local notation "unimodular" =>
  (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
set_option hygiene false in
local notation "modulusP" => modularCharacter_standardParabolicPoints hG hi hν I rfl
  (RationalPointFamily.rootSet_subset i ν I)
set_option hygiene false in
local notation "weightSmooth" =>
  isSmoothFiniteTorusFunction_standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hirr hreg
set_option hygiene false in
local notation "nG" => rationalValuationCoordinatesHom G hG
set_option hygiene false in
local notation "matrixA" => leviValuationRestrictionMatrix hG hi hν I
set_option hygiene false in
local notation "nK" =>
  (fun k hk => rationalValuationCoordinatesHom_eq_one_of_mem_compact hG hKc hk)
set_option hygiene false in
local notation "nU" =>
  (fun u hu => rationalValuationCoordinatesHom_eq_one_of_mem_standardUnipotent hG hi hν I hu)
set_option hygiene false in
local notation "nM" =>
  (fun m z => leviRationalUnitaryCoordinates_symm_finiteTorusMonomial_apply hG hi hν I m z)
set_option hygiene false in
local notation "modulusU" => isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl
set_option hygiene false in
local notation "leviData" =>
  rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc
set_option hygiene false in
local notation "minimalModulusK" =>
  (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp)

set_option hygiene false in
local notation "centralControl" => orbitSectionLevelCentralControl decomp closedU closedP K hKc
  factorization unimodular modulusP νM π normContinuous projectionContinuous coordinates
  CM hCM mu hsq rhoX W (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
  (leviRationalUnitaryCoordinates hG hi hν I).continuous weightSmooth nG matrixA nK nU nM
  modulusU leviData hPK hMK minimalModulusK coefficientXiBound
  (compactOpenCofinal_standardLevi I hKc)

/-- A continuous input seminorm for the exact source-normalized packet's central
decay, with the lower coefficient bound derived from square integrability under
explicit intrinsic-Levi structural data. -/
def standardLeviPlancherelPacketCentralControl (H : OpenSubgroup (rationalPoints G))
    (hHK : H ≤ K) (r : ℝ) :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    Seminorm ℂ (SectionLevel H) := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  let := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := rootsI) hKc
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  exact centralControl H hHK r

/-- Uniform central decay for the original packet and its original source-normalized
character and orbit measures. -/
theorem norm_standardLeviPlancherelPacket_le_centralControl :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (H : OpenSubgroup (rationalPoints G)) (hHK : H ≤ K) (r : ℝ)
      (q : SectionLevel H) (g : rationalPoints G),
      ‖packet (includeLevel H q) g‖ ≤
        standardLeviPlancherelPacketCentralControl hG hi hν I hζ s hs hindex π mu hsq
          hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
          hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ
          hMK hK0Lc hbasis hcover H hHK r q * rationalXi hKc hPK g *
            (1 + ‖rationalValuationCoordinates G hG g‖) ^ (-r) := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  let := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := rootsI) hKc
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  intro H hHK r q g
  exact norm_levelOrbitWavePacket_le_centralControl decomp closedU closedP K hKc factorization
    unimodular modulusP νM π normContinuous projectionContinuous coordinates CM hCM mu hsq rhoX W
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous weightSmooth nG matrixA nK nU nM
    modulusU leviData hPK hMK minimalModulusK coefficientXiBound
    (compactOpenCofinal_standardLevi I hKc) H hHK r q g

/-- The controlling seminorm is continuous in the existing source-level topology. -/
theorem continuous_standardLeviPlancherelPacketCentralControl :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (H : OpenSubgroup (rationalPoints G)) (hHK : H ≤ K) (r : ℝ),
      Continuous (standardLeviPlancherelPacketCentralControl hG hi hν I hζ s hs hindex π mu hsq
        hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
        hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ
        hMK hK0Lc hbasis hcover H hHK r) := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  let := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := rootsI) hKc
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  intro H hHK r
  exact continuous_orbitSectionLevelCentralControl decomp closedU closedP K hKc factorization
    unimodular modulusP νM π normContinuous projectionContinuous coordinates CM hCM mu hsq rhoX W
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous weightSmooth nG matrixA nK nU nM
    modulusU leviData hPK hMK minimalModulusK coefficientXiBound
    (compactOpenCofinal_standardLevi I hKc) H hHK r

end Langlands.HarishChandraSchwartz
