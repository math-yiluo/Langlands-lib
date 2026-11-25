import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialPacketCompact
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionSpecialCompact
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketWeakReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTermDecayProof

/-! # Source-normalized synthesis from the weak bounds at the common compact -/

noncomputable section

set_option maxRecDepth 10000
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

local instance standardLeviPacketSpecialAssemblyAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketSpecialAssemblyAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketSpecialAssemblyFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketSpecialAssemblyTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketSpecialAssemblyNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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
local notation "weakAt[" hc "," hp "," J "," hA "]" => RationalOrbitLevelWeakPacketRapid
  hG hi hν I hc hp π CM hCM mu hsq J hA ρ rhoX W
set_option hygiene false in
local notation "jRoots[" J "]" => RationalPointFamily.rootSet i ν J
set_option hygiene false in
local notation "leviFactors[" L "," J "]" => IsIwasawaPair
  ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
  ((L : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν J))


/-- The original weak estimates on the proper faces at the chosen packet compact. -/
def StandardLeviPacketWeakBoundsAt
    {L : OpenSubgroup (rationalPoints G)} (hLc : IsCompact (L : Set (rationalPoints G)))
    (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) (L : Subgroup (rationalPoints G))) : Prop :=
  letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  ∀ J : Finset (RationalPointFamily.SimpleRoot i ν), jRoots[J] ⊂ simpleRelativeRoots i ν →
    ∀ {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
      (hA : IsCompatibleStandardSplitComponent i ν (jRoots[J]) A qA),
      weakAt[hLc, hPL, J, hA]

set_option maxHeartbeats 2500000 in
/-- The exact synthesis conclusion from the weak bounds at the common
special compact. The constant-term threshold and positive estimates are
supplied by their published proofs. -/
theorem standardLeviPlancherelWavePacketSourceNormalized_of_specialCompact_weakBounds
    (hspecial : HasSpecialPacketCompact hi ν)
    (hweak : ∀ (L : OpenSubgroup (rationalPoints G)) (hLc : IsCompact (L : Set (rationalPoints G)))
      (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) (L : Subgroup (rationalPoints G))),
      WeakExpansion.IsSpecialVertexCompact ν hi L →
      SimultaneousStandardBasisAt i ν (L : Subgroup (rationalPoints G)) →
      StandardLeviCartanCovering F i ν ∅ (L : Subgroup (rationalPoints G)) →
      StandardLeviIwasawaFactorsAt (i := i) (ν := ν) (L : Subgroup (rationalPoints G)) →
      HasWeylRepresentatives i (L : Subgroup (rationalPoints G)) →
      StandardLeviPacketWeakBoundsAt hG hi hν I hζ s hs hindex π mu hsq hRefl hCST
        Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse
        hDReverseΩ hD hne hirr hreg ρ hLc hPL) :
    StandardLeviPlancherelWavePacketSourceNormalizedStatement hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse
      hDReverseΩ hD hne hirr hreg hKc hPK ρ := by
  classical
  obtain ⟨L, hLc, hspecialL, hIwa, hbasis, hcover, hLevi⟩ := hspecial
  have hPL := isIwasawaPair_of_pointProductEqualities (hIwa.2.2.1 ∅ (Set.empty_subset _))
  obtain ⟨hFactors, hWeyl⟩ := WeakExpansion.standardLeviIwasawaFactorsAt_and_weylRepresentatives_of_special
    hG hi hν hspecialL hPL
  have hweakL := hweak L hLc hPL hspecialL hbasis (hLevi ∅ (Set.empty_subset _)) hFactors hWeyl
  have hterms : StandardLeviPacketWeakConstantTermInputs hG hi hν I hζ s hs hindex π mu hsq
      hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
      hneReverse hDReverseΩ hD hne hirr hreg ρ hLc hPL hFactors := by
    intro J hJ A qA hA
    exact ⟨rationalOrbitConstantTermThreshold hG hi hν I hLc hPL π CM hCM mu hsq J hA,
      rationalOrbitPositiveConstantTermDecay hG hi hν I hLc hPL π CM hCM mu hsq J hA
        (hFactors (jRoots[J]) (RationalPointFamily.rootSet_subset i ν J)),
      hweakL J hJ hA⟩
  let := hi.isSplitSubtorus.1.finite_realCocharacterSpace
  have : Module.Free ℝ (RealTorusSpace.V S) := Module.Free.of_divisionRing ℝ _
  let b := Module.finBasis ℝ (RealTorusSpace.V S)
  let N := (normSeminorm ℝ (Fin (Module.finrank ℝ (RealTorusSpace.V S)) → ℝ)).comp
    b.equivFun.toLinearMap
  have hN (v : RealTorusSpace.V S) (hv : N v = 0) : v = 0 := by
    apply b.equivFun.injective
    rw [LinearEquiv.map_zero]
    exact norm_eq_zero.mp hv
  have hest := standardLeviPacketDerivativeEstimates_of_weakConstantTerms
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
    hKc hPK ρ hLc hPL hbasis hcover hLevi hFactors N hN hterms
  exact standardLeviPlancherelWavePacketSourceNormalized_of_estimates
    hG hi hν I hζ s hs hindex π mu hsq hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg hKc hPK ρ hest

end Langlands.HarishChandraSchwartz
