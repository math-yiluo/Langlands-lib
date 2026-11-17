import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacketSchwartz

/-! # Elementary regularity of source-normalized standard-Levi wave packets -/

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

local instance standardLeviPacketRegularityAffineHom : IsAffineHom 𝐋.X.hom :=
  leviScheme_isAffineHom i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketRegularityAffine : IsAffine 𝐋.X.left :=
  isAffine_of_isAffineHom 𝐋.X.hom
local instance standardLeviPacketRegularityFiniteType : LocallyOfFiniteType 𝐋.X.hom :=
  leviScheme_locallyOfFiniteType i ν (RationalPointFamily.rootSet i ν I)
local instance standardLeviPacketRegularityTopology : TopologicalSpace (rationalPoints 𝐋) :=
  rationalPointTopology F 𝐋.X
local instance standardLeviPacketRegularityNonarchimedean : NonarchimedeanGroup (rationalPoints 𝐋) :=
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

omit [IsAffine T.X.left] [(rationalPoints.map s).range.Normal] [BorelSpace (𝐌 ⧸ CM)] in
/-- At a fixed group point the actual weighted orbit coefficient is continuous.
This uses parameter smoothness and regularity of the actual density, without a Xi estimate. -/
theorem continuous_standardLeviPlancherelWavePacket_integrand
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (g : rationalPoints G) :
    Continuous (fun omega : Oπ => W omega *
      rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π CM hCM mu hsq q omega g) := by
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have hc := continuous_unitaryOrbitCoefficient (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    νM π (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv CM hCM mu hsq
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous q g
  have hw := continuous_standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
    hneReverse hDReverseΩ hD hne hirr hreg
  exact hw.mul hc

/-- The literal I.1-normalized weighted coefficient is pointwise Bochner integrable,
under precisely the source-normalized target's existing premises. -/
theorem integrable_standardLeviPlancherelWavePacket_integrand :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G),
      Integrable (fun omega : Oπ => W omega *
        rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π CM hCM mu hsq q omega g) dO := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  let : CompactSpace (unitaryUnramifiedCharacters νM) :=
    (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
  let := compactSpace_discreteSeriesOrbit CM hCM mu νM omegaπ
  let := isFiniteMeasure_standardLeviOrbitMeasure I s hs hindex mu omegaπ
  intro q g
  exact (continuous_standardLeviPlancherelWavePacket_integrand hG hi hν I hζ s hs π mu hsq
    hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
    hneReverse hDReverseΩ hD hne hirr hreg hKc hPK q g).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- One compact open subgroup makes the actual source-normalized packet bi-invariant.
The subgroup can depend on the smooth section and lies inside the packet subgroup K. -/
theorem exists_standardLeviPlancherelWavePacket_biInvariant :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
      ∃ H : OpenSubgroup (rationalPoints G), H ≤ K ∧ IsCompact (H : Set (rationalPoints G)) ∧
        ∀ (k l : H) (g : rationalPoints G),
          packet q ((k : rationalPoints G) * g * (l : rationalPoints G)) = packet q g := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  intro q
  exact exists_rationalInducedOrbitWavePacket_biInvariant hG hi hν I hKc hPK π CM hCM mu hsq
    rhoX W q

/-- Algebraic synthesis by the actual source-normalized packet, with values in functions.
Compact-orbit integrability proves additivity without coefficient Xi or Levi Iwasawa inputs. -/
def standardLeviPlancherelWavePacketLinear :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π →ₗ[ℂ] (rationalPoints G → ℂ) := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  refine { toFun := packet, map_add' := ?_, map_smul' := ?_ }
  · intro q r
    funext g
    change packet (q + r) g = packet q g + packet r g
    simp only [standardLeviPlancherelWavePacket_apply]
    rw [← integral_add
      (integrable_standardLeviPlancherelWavePacket_integrand hG hi hν I hζ s hs hindex π mu hsq
        hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
        hneReverse hDReverseΩ hD hne hirr hreg hKc hPK q g)
      (integrable_standardLeviPlancherelWavePacket_integrand hG hi hν I hζ s hs hindex π mu hsq
        hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
        hneReverse hDReverseΩ hD hne hirr hreg hKc hPK r g)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
    simp only [map_add, Pi.add_apply, LocallyConstant.coe_add]
    ring
  · intro c q
    funext g
    exact rationalInducedOrbitWavePacket_smul hG hi hν I hKc hPK π CM hCM mu hsq rhoX W c q g

/-- The algebraic synthesis map has the literal packet as its underlying function. -/
theorem standardLeviPlancherelWavePacketLinear_apply :
    letI := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
    ∀ (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G),
      standardLeviPlancherelWavePacketLinear hG hi hν I hζ s hs hindex π mu hsq
        hRefl hCST Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse
        hneReverse hDReverseΩ hD hne hirr hreg hKc hPK q g = packet q g := by
  let := finite_standardLeviDiscreteSeriesStabilizer I s hs hindex mu omegaπ
  intro q g
  rfl

end Langlands.HarishChandraSchwartz
