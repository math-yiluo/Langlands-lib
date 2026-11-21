import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviWavePacketComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacket
import Langlands.Representation.Plancherel.StandardLeviPlancherelWeightFullRoot

/-! # Change of variables in the actual group-Levi wave packet -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)
set_option hygiene false in
local notation "νG" => (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν Finset.univ
set_option hygiene false in
local notation "sL" => rationalFullLeviSplitComponent hG hi hν s
set_option hygiene false in
local notation "hsL" => isSplitComponent_rationalFullLeviSplitComponent hG hi hν s hs
set_option hygiene false in
local notation "A" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hA" => hs.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "B" => rationalLeviSplitCenter Finset.univ sL
set_option hygiene false in
local notation "hB" => rationalLeviSplitCenter_le_center Finset.univ sL hsL
set_option hygiene false in
local notation "eG" => rationalFullLeviLiteralPointEquiv hG hi hν

variable [(A).Normal] [(B).Normal] [(rationalPoints.map sL).range.Normal]
  [MeasurableSpace (rationalPoints G ⧸ A)] [BorelSpace (rationalPoints G ⧸ A)]
  [MeasurableSpace (𝐌 ⧸ B)] [BorelSpace (𝐌 ⧸ B)]
  (mu : Measure (rationalPoints G ⧸ A)) [mu.IsHaarMeasure]

set_option hygiene false in
local notation "muM" => rationalFullLeviQuotientHaar hG hi hν s mu

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
  (hsq : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation mu)

set_option hygiene false in
local notation "πM" => IrreducibleAdmissibleRep.pullback eG π
set_option hygiene false in
local notation "ω" => discreteSeriesClass A hA mu π hsq

set_option hygiene false in
local notation "hsqM" => rationalFullLeviPullback_isSquareIntegrable hG hi hν s hs mu π hsq
set_option hygiene false in
local notation "ωM" => discreteSeriesClass B hB muM πM hsqM
set_option hygiene false in
local notation "eO" => rationalFullLeviOrbitHomeomorph hG hi hν s hs mu ω

variable {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "sections" =>
  rationalInducedSmoothOrbitSections hG hi hν Finset.univ hKc hPK πM
set_option hygiene false in
local notation "coeff" =>
  rationalInducedOrbitCoefficientMap hG hi hν Finset.univ hKc hPK πM B hB muM hsqM

set_option hygiene false in
local notation "OM" => discreteSeriesOrbit B hB muM νM ωM
set_option hygiene false in
local notation "OG" => discreteSeriesOrbit A hA mu νG ω
set_option hygiene false in
local notation "tensor" => rationalFullLeviOrbitCoefficientTensor hG hi hν s hs mu π hsq hKc hPK

omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
/-- The full-Levi orbit homeomorphism with its target read as the orbit
of the pulled-back inducing representative. -/
def rationalFullLeviInducingOrbitHomeomorph : OG ≃ₜ OM := eO

set_option hygiene false in
local notation "e" => rationalFullLeviInducingOrbitHomeomorph hG hi hν s hs mu π hsq

set_option maxHeartbeats 300000 in
omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
private theorem fullLeviOrbitCoefficient_comp
    (q : sections) (g : rationalPoints G) :
    (fun x : OM => coeff q x g) ∘ e =
      fun x : OG => coefficientTensorMap (Quotient.out x.val.val).obj (tensor q x) g := by
  funext x
  rw [Function.comp_apply]
  have he : e x = (eO) x := by
    unfold rationalFullLeviInducingOrbitHomeomorph
    rfl
  refine (congrArg (fun y : OM => coeff q y g) he).trans ?_
  have ht := congrArg (fun f : LocallyConstant (rationalPoints G) ℂ => f g)
    (coefficientTensorMap_rationalFullLeviOrbitCoefficientTensor
      hG hi hν s hs mu π hsq hKc hPK q x)
  unfold rationalFullLeviAmbientOrbitCoefficient at ht
  with_reducible_and_instances exact ht.symm

omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
set_option maxHeartbeats 300000 in
/-- Pointwise evaluation of the transported full-Levi section coefficient
is continuous in the ambient discrete-series orbit. -/
theorem continuous_rationalFullLeviOrbitCoefficientTensor
    (q : sections) (g : rationalPoints G) :
    Continuous (fun x : OG =>
      coefficientTensorMap (Quotient.out x.val.val).obj (tensor q x) g) := by
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν Finset.univ
  have hc := continuous_unitaryOrbitCoefficient (G := rationalPoints G) (M := 𝐌)
    (isSemidirectDecomposition_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν Finset.univ))
    (isClosed_standardParabolicPoints_rootSet hG hi hν Finset.univ) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν _ hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν Finset.univ rfl
      (RationalPointFamily.rootSet_subset i ν Finset.univ))
    νM πM (RationalPointFamily.continuous_leviRationalNormCharacters i ν Finset.univ)
    (continuous_projection_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ) _)
    (leviRationalUnitaryCoordinates hG hi hν Finset.univ).toMulEquiv B hB muM hsqM
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν Finset.univ)
    (leviRationalUnitaryCoordinates hG hi hν Finset.univ).continuous q g
  have hL : Continuous (fun x : OM => coeff q x g) := by
    unfold rationalInducedOrbitCoefficientMap
    with_reducible_and_instances exact hc
  have h := hL.comp (e).continuous
  rwa [fullLeviOrbitCoefficient_comp hG hi hν s hs mu π hsq hKc hPK q g] at h

set_option hygiene false in
local notation "hindexG" => finiteIndex_splitValuationImage_of_isSplitComponent hG s hs
set_option hygiene false in
local notation "hindexM" => finiteIndex_splitValuationImage_of_isSplitComponent
  (isConnectedReductive_leviScheme_rootSet hG hi hν Finset.univ) sL hsL
set_option hygiene false in
local notation "rhoX" => standardLeviUnitaryUnramifiedCharacterHaar Finset.univ sL hsL hindexM
set_option hygiene false in
local notation "dOG" => rationalNormalizedDiscreteSeriesOrbitMeasure s
  hs.isCentralSplitTorus.isCentral mu hindexG ω
set_option hygiene false in
local notation "packetG" => rationalOrbitWavePacket s hs.isCentralSplitTorus.isCentral
  mu hindexG ω

set_option maxHeartbeats 300000 in
/-- A full-root section with constant weight one has the ambient packet
integral with the source-normalized orbit measure. -/
theorem rationalInducedOrbitWavePacket_fullLevi_eq_ambient
    (w : OM → ℂ) (hw : ∀ x, w x = 1) (q : sections) (g : rationalPoints G) :
    letI := finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexM muM ωM
    rationalInducedOrbitWavePacket hG hi hν Finset.univ hKc hPK πM B hB muM hsqM rhoX w q g =
      packetG (tensor q) g := by
  let := finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexM muM ωM
  rw [rationalInducedOrbitWavePacket_apply, rationalOrbitWavePacket_apply]
  have hw' : (fun x : OM => w x * coeff q x g) = fun x : OM => coeff q x g := by
    funext x
    exact (congrArg (fun z : ℂ => z * coeff q x g) (hw x)).trans (one_mul _)
  rw [hw']
  have hm := map_rationalFullLeviOrbitHomeomorph_measure hG hi hν s hs mu ω
  let : Finite (discreteSeriesStabilizer B hB muM νM
      (rationalFullLeviDiscreteSeriesClass hG hi hν s hs mu ω)) :=
    finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexM muM ωM
  rw [standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq] at hm
  have hmap : Measure.map e dOG = discreteSeriesOrbitMeasure νM B hB muM ωM rhoX := hm
  rw [← hmap]
  have he := (e).measurableEmbedding.integral_map («μ» := dOG) (fun x : OM => coeff q x g)
  have hc := congrArg (fun f : OG → ℂ => ∫ x, f x ∂dOG)
    (fullLeviOrbitCoefficient_comp hG hi hν s hs mu π hsq hKc hPK q g)
  simp only [Function.comp_def] at hc
  with_reducible_and_instances exact he.trans hc

section ActualWeight

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false

open Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.RationalDynamicSource Langlands.Plancherel.RationalPlancherelDensity

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

variable {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν Finset.univ) ζ)

set_option hygiene false in
local notation "χζ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "AπM" =>
  SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν Finset.univ hζ) (πM).obj

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (Ks : OpenSubgroup (RationalPoint F G.X))
  (hKs : IsCompact (Ks : Set (RationalPoint F G.X)))
  (hPKs : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χζ, ∃ k : Ks, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppKs : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χζ, ∃ k : Ks,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χζ hRefl hCST hG Ks hKs hPKs hOppKs AπM)
  (qrev : ReverseContinuation χζ hRefl hCST hG Ks hKs hPKs hOppKs AπM)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χζ Ks hKs AπM)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χζ Ks hKs AπM)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χζ) (radical_isClosed χζ)
      (leviNormCharacters χζ) (parameterTransport χζ z) AπM).IsIrreducible)

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χζ hRefl hCST hG Ks hKs hPKs hOppKs AπM
  p qrev hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

variable (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)

set_option hygiene false in
local notation "W" => standardLeviPlancherelWeight hG hi hν Finset.univ hζ πM B hB muM hsqM hRefl hCST
  Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
  hD hne hirr hreg

/-- With Waldspurger's actual Plancherel density, the standard full-root
packet is the transported ambient packet. -/
theorem standardLeviPlancherelWavePacket_fullLevi_eq_ambient
    (q : sections) (g : rationalPoints G) :
    letI := finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexM muM ωM
    standardLeviPlancherelWavePacket hG hi hν Finset.univ hζ πM B hB muM hsqM hRefl hCST
        Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse
        hDReverseΩ hD hne hirr hreg hKc hPK rhoX q g = packetG (tensor q) g := by
  let := finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexM muM ωM
  have hw := standardLeviPlancherelWeight_eq_one_of_rootSet_eq_simpleRelativeRoots
    hG hi hν Finset.univ hζ πM B hB muM hsqM hRefl hCST Ks hKs hPKs hOppKs p qrev
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
    (RationalPointFamily.rootSet_univ i ν) hreg
  unfold standardLeviPlancherelWavePacket
  have h := rationalInducedOrbitWavePacket_fullLevi_eq_ambient hG hi hν s hs mu π hsq hKc hPK
    W hw q g
  with_reducible_and_instances exact h

end ActualWeight

end Langlands.HarishChandraSchwartz
