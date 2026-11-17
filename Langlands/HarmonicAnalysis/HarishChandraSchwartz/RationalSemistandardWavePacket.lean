import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardPlancherelWeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardCharacterMeasure
import Langlands.Representation.Plancherel.LeviCompactCoefficients
import Langlands.Representation.Plancherel.ProductInducedOrbitCoefficientSmoothness
import Langlands.Representation.Aubert.General.SemidirectModularCharacter
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction

/-! # Actual semistandard orbit coefficients and source wave packets -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

open Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

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
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {t : SemistandardSpectralIndex i} (hG : IsConnectedReductive G)
  (model : LeviModel t) (r : CocharacterPresentation hG t) (d : CompactData t)

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance packetModelAffineHom : IsAffineHom model.scheme.X.hom := model.reductive.isAffineHom
local instance packetModelAffine : IsAffine model.scheme.X.left := isAffine_of_isAffineHom model.scheme.X.hom
local instance packetModelSmooth : Smooth model.scheme.X.hom := model.reductive.smooth
local instance packetModelFiniteType : LocallyOfFiniteType model.scheme.X.hom := inferInstance
local instance packetModelTopology : TopologicalSpace (rationalPoints model.scheme) :=
  rationalPointTopology F model.scheme.X

omit [LocallyOfFiniteType G.X.hom] in
include model in
/-- Closedness of the exact literal Levi follows from its actual closed model. -/
theorem isClosed_levi_of_model : IsClosed (levi t : Set (rationalPoints G)) :=
  isClosed_rationalPoint_subgroup F t.levi model.inclusion model.represents model.closed

local instance packetLeviLocallyCompact : LocallyCompactSpace (levi t) :=
  (isClosed_levi_of_model (chosenLeviModel t)).locallyCompactSpace
local instance packetParabolicLocallyCompact : LocallyCompactSpace (parabolic t) :=
  (isClosed_parabolic t).locallyCompactSpace

include model in
/-- Actual reductive unimodularity on the literal Levi. -/
theorem levi_modularCharacter (x : levi t) : Measure.modularCharacter x = 1 := by
  have hm := RationalPointFamily.rationalReductiveUnimodularity F model.scheme model.reductive
    standardCocharacter (model.pointHomeomorph.symm x)
  simpa only [ContinuousMulEquiv.apply_symm_apply] using
    (modularCharacter_continuousMulEquiv model.pointHomeomorph
      (model.pointHomeomorph.symm x)).trans hm

include hG r in
/-- The actual dynamic radical theorem applies to the entire intrinsic triple. -/
theorem radical_isUnimodular : IsUnimodularModulus (radical t) (isClosed_radical t) := by
  rcases r with ⟨zeta, heq⟩
  cases heq
  exact DynamicOppositeCanonicalScalar.radical_unimodular
    (CommGroupScheme.groupHom zeta ≫ i) hG

include hG model r d in
/-- The normalized parabolic modulus is determined by these proved unimodular factors. -/
theorem parabolic_modularCharacter (x : parabolic t) : Measure.modularCharacter x =
    (HaarModulus.closedRestrictCharacter (radical t) (isClosed_radical t)
      (parabolic t) (decomposition t).le_normalizer x : ℝ≥0) := by
  have : LocallyCompactSpace (radical t) := (isClosed_radical t).locallyCompactSpace
  simpa only [HaarModulus.closedRestrictCharacter_eq] using
    (decomposition t).modularCharacter_eq_restrictCharacter_of_unimodular
      d.projection_continuous (levi_modularCharacter model)
      (radical_isUnimodular hG r) x

include hG in
/-- Actual ambient rational-point unimodularity, with the published theorem. -/
theorem ambient_modularCharacter (x : rationalPoints G) : Measure.modularCharacter x = 1 :=
  RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter x

namespace SourcePacket

section Coefficients

variable (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t))
  (C : Subgroup (levi t)) [C.Normal] (hC : C ≤ Subgroup.center (levi t))
  [MeasurableSpace (levi t ⧸ C)] (mu : Measure (levi t ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation mu)

/-- The existing actual orbit coefficient on this intrinsic smooth family. -/
def coefficientMap : smoothOrbitSections model d pi →ₗ[ℂ]
    (discreteSeriesOrbit C hC mu model.normCharacters
      (discreteSeriesClass C hC mu pi hsq) → LocallyConstant (rationalPoints G) ℂ) :=
  unitaryOrbitCoefficientMap (decomposition t) (isClosed_radical t) (isClosed_parabolic t)
    d.compact d.isCompact d.factorization (ambient_modularCharacter hG)
    (parabolic_modularCharacter hG model r d) model.normCharacters pi
    model.continuous_normCharacters d.projection_continuous C hC mu hsq
    model.unitaryCoordinates.toMulEquiv

/-- Coherent representative change preserves the exact coefficient function. -/
theorem coefficientMap_representative (v : smoothOrbitSections model d pi)
    (A : UnitaryOrbitRepresentative model.normCharacters pi) :
    coefficientMap hG model r d pi C hC mu hsq v
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit model.normCharacters pi C hC mu hsq A) =
    unitaryOrbitRepresentativeCoefficientMap (decomposition t) (isClosed_radical t)
      (isClosed_parabolic t) d.compact d.isCompact d.factorization
      (ambient_modularCharacter hG) (parabolic_modularCharacter hG model r d)
      model.normCharacters pi d.projection_continuous A (v.val A) :=
  unitaryOrbitCoefficientMap_representative (decomposition t) (isClosed_radical t)
    (isClosed_parabolic t) d.compact d.isCompact d.factorization
    (ambient_modularCharacter hG) (parabolic_modularCharacter hG model r d)
    model.normCharacters pi model.continuous_normCharacters d.projection_continuous
    C hC mu hsq model.unitaryCoordinates.toMulEquiv v A

/-- At fixed g, the coefficient is continuous on the actual orbit quotient. -/
theorem continuous_coefficient (v : smoothOrbitSections model d pi) (g : rationalPoints G) :
    Continuous (fun omega => coefficientMap hG model r d pi C hC mu hsq v omega g) :=
  continuous_unitaryOrbitCoefficient (decomposition t) (isClosed_radical t)
    (isClosed_parabolic t) d.compact d.isCompact d.factorization
    (ambient_modularCharacter hG) (parabolic_modularCharacter hG model r d)
    model.normCharacters pi model.continuous_normCharacters d.projection_continuous
    model.unitaryCoordinates.toMulEquiv C hC mu hsq model.unitaryCoordinates_hasLaurent
    model.unitaryCoordinates.continuous v g

/-- The exact positive-Levi source normalization agrees with the original
coefficient map after the published actual tensor comparison. -/
theorem coefficientMap_leviNormalization (v : smoothOrbitSections model d pi)
    (A : UnitaryOrbitRepresentative model.normCharacters pi) :
    coefficientMap hG model r d pi C hC mu hsq v
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit model.normCharacters pi C hC mu hsq A) =
    CompactInduction.leviCoefficientMap (decomposition t) (isClosed_radical t) A.val.obj
      d.compact (radical_isUnimodular hG r) d.isCompact (isClosed_parabolic t)
      d.projection_continuous
      (fun g => by
        obtain ⟨p, k, hg⟩ := d.factorization g
        exact ⟨p, p.property, k, k.property, hg⟩)
      (ambient_modularCharacter hG) (parabolic_modularCharacter hG model r d) A.val.property.2
      (productInducedCoefficientLeviEquiv (decomposition t) (isClosed_radical t) A.val.obj
        (radical_isUnimodular hG r) (v.val A)) := by
  rw [coefficientMap_representative]
  exact (CompactInduction.leviCoefficientMap_compare (decomposition t) (isClosed_radical t)
    A.val.obj d.compact (radical_isUnimodular hG r) d.isCompact (isClosed_parabolic t)
    d.projection_continuous _ (ambient_modularCharacter hG)
    (parabolic_modularCharacter hG model r d) A.val.property.2 (v.val A)).symm

end Coefficients

section SourceNormalized

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
  (a : A.toGrp ⟶ model.scheme) (ha : IsSplitComponent a)
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  [(model.splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
  [MeasurableSpace (levi t ⧸ model.splitCenter a)] [BorelSpace (levi t ⧸ model.splitCenter a)]
  (mu : Measure (levi t ⧸ model.splitCenter a)) [mu.IsHaarMeasure]
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t))
  (hsq : IsSquareIntegrableModCentralSubgroup (model.splitCenter a)
    (model.splitCenter_le_center a ha) pi.obj.representation mu)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom r.cocharacter ≫ i
set_option hygiene false in
local notation "MS" => DynamicOppositeStandardIntertwining.parameterScheme χ
set_option hygiene false in
local notation "νL" => DynamicOppositeStandardIntertwining.normCharacters χ
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive χ hG
set_option hygiene false in
local notation "C" => model.splitCenter a
set_option hygiene false in
local notation "hC" => model.splitCenter_le_center a ha
set_option hygiene false in
local notation "omega0" => discreteSeriesClass C hC mu pi hsq
set_option hygiene false in
local notation "Opi" => discreteSeriesOrbit C hC mu model.normCharacters omega0
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback r.literalLeviHomeomorph pi.obj
set_option hygiene false in
local notation "eta" => SourceMeasure.normalizedOrbitMeasure model a ha hindex mu omega0

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (Ks : OpenSubgroup (RationalPoint F G.X))
  (hKs : IsCompact (Ks : Set (RationalPoint F G.X)))
  (hPKs : ∀ g : RationalPoint F G.X,
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χ, ∃ k : Ks, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppKs : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : Ks,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
  (q : ReverseContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ Ks hKs Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ Ks hKs Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (DynamicOppositeStandardIntertwining.decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

-- The canonical scalar `j_P` of the inducing representation `pi ∘ e`.
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr


variable (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)

set_option hygiene false in
local notation "W" => SourceDensity.orbitPlancherelWeight model r pi C hC mu hsq hRefl hCST
  Ks hKs hPKs hOppKs p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
  hD hne hirr hreg

set_option hygiene false in
local notation "E" => coefficientMap hG model r d pi C hC mu hsq

omit [IsAffine A.X.left] [(rationalPoints.map a).range.Normal]
  [BorelSpace (levi t ⧸ model.splitCenter a)] in
/-- Actual compactness uses the model's finite circle coordinates and the actual orbit quotient. -/
theorem sourceOrbit_compactSpace : CompactSpace Opi := by
  let : CompactSpace (unitaryUnramifiedCharacters model.normCharacters) :=
    model.unitaryCoordinates.symm.toHomeomorph.compactSpace
  exact compactSpace_discreteSeriesOrbit C hC mu model.normCharacters omega0

/-- The actual pointwise VI.3 integrand is continuous on a compact orbit and
integrable for the finite source-scaled measure. No full Schwartz estimate is used. -/
theorem integrable_wavePacketIntegrand (v : smoothOrbitSections model d pi) (g : rationalPoints G) :
    Integrable (fun omega : Opi => W omega * E v omega g) eta := by
  let := sourceOrbit_compactSpace model a ha mu pi hsq
  have hw := SourceDensity.continuous_orbitPlancherelWeight model r pi C hC mu hsq hRefl hCST
    Ks hKs hPKs hOppKs p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    hD hne hirr hreg
  have hcont := hw.mul (continuous_coefficient hG model r d pi C hC mu hsq v g)
  exact (BoundedContinuousFunction.mkOfCompact ⟨_, hcont⟩).integrable eta

/-- The actual source-normalized semistandard wave packet, with the fixed actual density. -/
def rawWavePacket (v : smoothOrbitSections model d pi) (g : rationalPoints G) : ℂ :=
  ∫ omega : Opi, W omega * E v omega g ∂eta

/-- The source orbit measure is exactly the literal measure in the existing
integral API. The displayed finite instance follows from the source-measure adapter. -/
theorem rawWavePacket_eq_literalMeasure
    [Finite (discreteSeriesStabilizer C hC mu model.normCharacters omega0)]
    (v : smoothOrbitSections model d pi) (g : rationalPoints G) :
    rawWavePacket hG model r d a ha hindex mu pi hsq hRefl hCST Ks hKs hPKs hOppKs p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg v g =
    ∫ omega : Opi, W omega * E v omega g
      ∂discreteSeriesOrbitMeasure model.normCharacters C hC mu omega0
        (SourceMeasure.unitaryCharacterHaar model a ha hindex) := by
  unfold rawWavePacket
  rw [SourceMeasure.normalizedOrbitMeasure_eq]

/-- Homogeneity of the actual source packet. -/
theorem rawWavePacket_smul (c : ℂ) (v : smoothOrbitSections model d pi) (g : rationalPoints G) :
    rawWavePacket hG model r d a ha hindex mu pi hsq hRefl hCST Ks hKs hPKs hOppKs p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg (c • v) g =
    c * rawWavePacket hG model r d a ha hindex mu pi hsq hRefl hCST Ks hKs hPKs hOppKs p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg v g := by
  unfold rawWavePacket
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  simp only [map_smul, Pi.smul_apply, LocallyConstant.coe_smul, smul_eq_mul]
  ring

/-- Additivity uses the proved pointwise integrability of these actual integrands. -/
theorem rawWavePacket_add (v w : smoothOrbitSections model d pi) (g : rationalPoints G) :
    rawWavePacket hG model r d a ha hindex mu pi hsq hRefl hCST Ks hKs hPKs hOppKs p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg (v + w) g =
    rawWavePacket hG model r d a ha hindex mu pi hsq hRefl hCST Ks hKs hPKs hOppKs p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg v g +
    rawWavePacket hG model r d a ha hindex mu pi hsq hRefl hCST Ks hKs hPKs hOppKs p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg w g := by
  unfold rawWavePacket
  rw [← integral_add
    (integrable_wavePacketIntegrand hG model r d a ha hindex mu pi hsq hRefl hCST
      Ks hKs hPKs hOppKs p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
      hD hne hirr hreg v g)
    (integrable_wavePacketIntegrand hG model r d a ha hindex mu pi hsq hRefl hCST
      Ks hKs hPKs hOppKs p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
      hD hne hirr hreg w g)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  simp only [map_add, Pi.add_apply, LocallyConstant.coe_add]
  ring

/-- The actual source packet as a complex-linear function-valued map. -/
def rawWavePacketLinear : smoothOrbitSections model d pi →ₗ[ℂ] (rationalPoints G → ℂ) where
  toFun := rawWavePacket hG model r d a ha hindex mu pi hsq hRefl hCST Ks hKs hPKs hOppKs p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
  map_add' v w := funext fun g => rawWavePacket_add hG model r d a ha hindex mu pi hsq hRefl hCST
    Ks hKs hPKs hOppKs p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    hD hne hirr hreg v w g
  map_smul' c v := funext fun g => rawWavePacket_smul hG model r d a ha hindex mu pi hsq hRefl hCST
    Ks hKs hPKs hOppKs p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    hD hne hirr hreg c v g

end SourceNormalized

end SourcePacket

end Langlands.HarishChandraSchwartz.RationalSemistandard
