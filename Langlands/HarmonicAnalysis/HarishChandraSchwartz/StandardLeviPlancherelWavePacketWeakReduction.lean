import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakPositivePacketAssembly
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketCompactChange

/-! # Reducing the original derivative estimates to the weighted weak terms -/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open Langlands.BruhatTits.SpecialCompact Langlands.Geometry.Building
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

local instance standardLeviPacketWeakReductionAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketWeakReductionAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketWeakReductionFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketWeakReductionTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketWeakReductionNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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

set_option hygiene false in
local notation "W" => standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
  Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
  hD hne hirr hreg
set_option hygiene false in
local notation "rhoX" => standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex
set_option hygiene false in
local notation "omegaπ" => discreteSeriesClass CM hCM mu π hsq
variable {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))

set_option hygiene false in
local notation "thresholdAt[" hc "," hp "," J "," hA "]" => RationalOrbitConstantTermThresholdStatement
  hG hi hν I hc hp π CM hCM mu hsq J hA
set_option hygiene false in
local notation "positiveAt[" hc "," hp "," J "," hA "," hMK "]" => RationalOrbitPositiveConstantTermDecayStatement
  hG hi hν I hc hp π CM hCM mu hsq J hA hMK
set_option hygiene false in
local notation "weakAt[" hc "," hp "," J "," hA "]" => RationalOrbitLevelWeakPacketRapid
  hG hi hν I hc hp π CM hCM mu hsq J hA ρ rhoX W
set_option hygiene false in
local notation "properAt[" hc "," hp "]" => StandardLeviPacketProperRegionDerivativeEstimates hG hi hν I hζ
  s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ
  hDReverse hneReverse hDReverseΩ hD hne hirr hreg hc hp ρ
set_option hygiene false in
local notation "jRoots[" J "]" => RationalPointFamily.rootSet i ν J
set_option hygiene false in
local notation "leviFactors[" L "," J "]" => IsIwasawaPair
  ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
  ((L : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν J))

variable {L : OpenSubgroup (rationalPoints G)} (hLc : IsCompact (L : Set (rationalPoints G)))
  (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) (L : Subgroup (rationalPoints G)))

/-- The three proper-parabolic inputs at the auxiliary compact for the
same source-normalized weight and orbit measure. -/
def StandardLeviPacketWeakConstantTermInputs
    (hFactors : ∀ J ⊆ simpleRelativeRoots i ν, leviFactors[L, J]) : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  ∀ J : Finset (RationalPointFamily.SimpleRoot i ν), jRoots[J] ⊂ simpleRelativeRoots i ν →
    ∀ {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
      (hA : IsCompatibleStandardSplitComponent i ν (jRoots[J]) A qA),
      thresholdAt[hLc, hPL, J, hA] ∧
        positiveAt[hLc, hPL, J, hA, hFactors jRoots[J] (RationalPointFamily.rootSet_subset i ν J)] ∧
        weakAt[hLc, hPL, J, hA]

/-- The threshold, positive decay and weighted weak bounds at one auxiliary
compact give the original source-normalized derivative estimate. -/
theorem standardLeviPacketDerivativeEstimates_of_weakConstantTerms
    (hbasis : SimultaneousStandardBasisAt i ν (L : Subgroup (rationalPoints G)))
    (hcover : RationalPointFamily.FiniteCartanCovering F i ν (L : Subgroup (rationalPoints G)))
    (hLevi : ∀ J ⊆ simpleRelativeRoots i ν,
      StandardLeviCartanCovering F i ν J (L : Subgroup (rationalPoints G)))
    (hFactors : ∀ J ⊆ simpleRelativeRoots i ν, leviFactors[L, J])
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0)
    (hterms : StandardLeviPacketWeakConstantTermInputs hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
      hneReverse hDReverseΩ hD hne hirr hreg ρ hLc hPL hFactors) :
    StandardLeviPacketDerivativeEstimates hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
      hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ := by
  classical
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let : CompactSpace (unitaryUnramifiedCharacters νM) :=
    (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
  let := compactSpace_discreteSeriesOrbit CM hCM mu νM omegaπ
  let := isFiniteMeasure_standardLeviOrbitMeasure I s hs hindex mu omegaπ
  have hw : Integrable W (discreteSeriesOrbitMeasure νM CM hCM mu omegaπ rhoX) :=
    (continuous_standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
      hneReverse hDReverseΩ hD hne hirr hreg).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hproperL : properAt[hLc, hPL] N := by
    intro J hJ δ hδ H hHL r
    have hJsub := RationalPointFamily.rootSet_subset i ν J
    have hMK := hFactors (jRoots[J]) hJsub
    have hbasisData := hbasis
    obtain ⟨B, hB, hstd⟩ := hbasisData
    obtain ⟨_, A, qA, hA, hmem⟩ := hstd (jRoots[J]) hJsub
    obtain ⟨ζ', hζ'⟩ := (standardCocharacter F G hG S i hi ν hν (jRoots[J]) hJsub).1
    obtain ⟨ht, hp, hwk⟩ := hterms J hJ hA
    have htLevel := rationalOrbitLevelConstantTermThreshold_of_perSection
      hG hi hν I hLc hPL π CM hCM mu hsq J hA hζ' hB hmem
      (ht hζ' L.isOpen hLc hB hmem hbasis hcover hLevi)
    have hpLevel := rationalOrbitLevelPositiveDecay_of_perSection
      hG hi hν I hLc hPL π CM hCM mu hsq J hA hζ' hB hmem N _
      (fun m => rationalLeviXi_nonneg hLc hMK (minimalLeviInclusion hG hi hν (jRoots[J]) m))
      (hp hζ' L.isOpen hLc hB hmem hbasis hcover hLevi N hN)
    have hpRapid := rationalOrbitLevelPositiveRapid_of_exponential
      hG hi hν I hLc hPL π CM hCM mu hsq J hA hMK N ρ
      hLc hbasis (hLevi ∅ (Set.empty_subset _)) hN hpLevel
    have hnorm := rationalOrbitLevelProperPacketRapid_of_weak_positive
      hG hi hν I hLc hPL π CM hCM mu hsq J hA N ρ rhoX W hw
      (integrable_standardLeviPlancherelWavePacket_integrand hG hi hν I hζ s hs hindex π mu hsq
        hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
        hneReverse hDReverseΩ hD hne hirr hreg hLc hPL) htLevel hpRapid hwk
    exact hnorm H hHL δ hδ r
  have hproperK := standardLeviPacketProperRegionDerivativeEstimates_of_compactChange
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
    hKc hPK hLc hPL ρ N hproperL
  have hchamber := standardLeviPacketChamberDerivativeEstimates_of_properRegions
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
    hKc hPK ρ hLc hbasis (hLevi ∅ (Set.empty_subset _))
    (hLevi (jRoots[I]) (RationalPointFamily.rootSet_subset i ν I)) N hN hproperK
  exact standardLeviPacketDerivativeEstimates_of_chamber
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
    hKc hPK ρ hLc hcover hchamber

end Langlands.HarishChandraSchwartz
