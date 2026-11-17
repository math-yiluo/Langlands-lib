import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardStandardSourceComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviPlancherelWavePacket
import Langlands.Representation.Plancherel.PlancherelOrbitWavePacketOrthogonality

/-! # Actual standard specialization of semistandard source constructions -/

noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.StandardPacketComparison

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

attribute [local instance]
  standardLeviPlancherelWeightLeviClosed standardLeviPlancherelWeightLeviAffine
  standardLeviPlancherelWeightLeviTopology leviLocallyOfFiniteType
  SourceMeasure.modelAffineHom SourceMeasure.modelAffine SourceMeasure.modelSmooth
  SourceMeasure.modelFiniteType SourceMeasure.modelTopology SourceMeasure.modelNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu) (I : Finset (RationalPointFamily.SimpleRoot i nu))
  {zeta : cocharacterLattice S}
  (hzeta : IsStandardCocharacter i nu (RationalPointFamily.rootSet i nu I) zeta)

open StandardSourceComparison

set_option hygiene false in
local notation "model" => standardLeviModel hG hi hnu I
set_option hygiene false in
local notation "rs" => presentation hG hi hnu I hzeta
set_option hygiene false in
local notation "nuM" => RationalPointFamily.leviRationalNormCharacters i nu I
set_option hygiene false in
local notation "M" => levi (standardIndex hG hi hnu I)

set_option hygiene false in
local notation "OldM" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I)) x}

variable {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "d" => standardCompactData hG hi hnu I hK hPK

section Coefficients

variable (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))
  (C : Subgroup M) [nC : C.Normal] (hC : C ≤ Subgroup.center M)
  [mC : MeasurableSpace (M ⧸ C)] (mu : Measure (M ⧸ C)) [hm : mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation mu)

/-- The actual semistandard coefficient uses exactly the existing standard normalization. -/
theorem coefficient_eq_standard : SourcePacket.coefficientMap hG model rs d pi C hC mu hsq =
    @rationalInducedOrbitCoefficientMap F _ _ _ _ S G _ _ i nu hG hi hnu I K hK hPK pi C
      (show (show Subgroup OldM from C).Normal from nC) hC
      (show MeasurableSpace (OldM ⧸ C) from mC)
      (show Measure (OldM ⧸ C) from mu)
      (show (show Measure (OldM ⧸ C) from mu).IsHaarMeasure from hm) hsq := by
  rfl

end Coefficients

section Source

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
  (a : A.toGrp ⟶ (model).scheme) (ha : IsSplitComponent a)
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  [nC : ((model).splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
  [mC : MeasurableSpace (M ⧸ (model).splitCenter a)] [BorelSpace (M ⧸ (model).splitCenter a)]
  (mu : Measure (M ⧸ (model).splitCenter a)) [hm : mu.IsHaarMeasure] [mu.IsInvInvariant]
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))
  (hsq : IsSquareIntegrableModCentralSubgroup ((model).splitCenter a)
    ((model).splitCenter_le_center a ha) pi.obj.representation mu)
  (q : OrbitPacketData rs pi)

set_option hygiene false in
local notation "C" => (model).splitCenter a
set_option hygiene false in
local notation "hC" => (model).splitCenter_le_center a ha
set_option hygiene false in
local notation "omega0" => discreteSeriesClass C hC mu pi hsq

/-- The standard character measure retains the source I.1 Haar normalization. -/
def standardCharacterHaar :=
  Measure.map
    (unitaryUnramifiedCharactersHomeomorph
      (RationalPointFamily.leviRationalPointHomeomorph i nu I)
      (fun psi => (rationalNormCharacters
        (Standard.leviScheme i nu (RationalPointFamily.rootSet i nu I)) psi).toMul))
    (rationalUnitaryUnramifiedCharacterHaar a ha.isCentralSplitTorus.isCentral hindex)

omit nC [(rationalPoints.map a).range.Normal] mC [BorelSpace (M ⧸ C)] in
/-- Specializing the actual model measure is exactly the existing standard point transport. -/
theorem characterHaar_eq_standard : SourceMeasure.unitaryCharacterHaar model a ha hindex =
    standardCharacterHaar hG hi hnu I a ha hindex := rfl

omit [mu.IsInvInvariant] in
/-- The actual source-scaled orbit measure has the standard orbit formula. -/
theorem orbitMeasure_eq_standard :
    letI := SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0
    SourceMeasure.normalizedOrbitMeasure model a ha hindex mu omega0 =
    discreteSeriesOrbitMeasure (model).normCharacters C hC mu omega0
      (standardCharacterHaar hG hi hnu I a ha hindex) := by
  let := SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0
  rw [SourceMeasure.normalizedOrbitMeasure_eq, characterHaar_eq_standard]

set_option maxHeartbeats 1800000 in
/-- The actual published standard orbit packet at the same source Haar and actual density. -/
def standardPacket :=
  letI := SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0
  @rationalInducedOrbitWavePacket F _ _ _ _ S G _ _ i nu hG hi hnu I K hK hPK pi C
    (show (show Subgroup OldM from C).Normal from nC) hC
    (show MeasurableSpace (OldM ⧸ C) from mC)
    (show Measure (OldM ⧸ C) from mu)
    (show (show Measure (OldM ⧸ C) from mu).IsHaarMeasure from hm) hsq
    (show Finite (discreteSeriesStabilizer C hC mu nuM omega0) from
      SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0)
    (standardCharacterHaar hG hi hnu I a ha hindex)
    (standardDensity hG hi hnu I hzeta pi C hC mu hsq q)

set_option maxHeartbeats 1800000 in
omit [mu.IsInvInvariant] in
/-- The actual source packet specializes to the published standard orbit packet. -/
theorem packet_eq_standard (v : smoothOrbitSections model d pi) (g : rationalPoints G) :
    q.packetLinear model d a ha hindex mu hsq v g =
      standardPacket hG hi hnu I hzeta hK hPK a ha hindex mu pi hsq q v g := by
  let := SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0
  change (∫ omega, SourceForm.orbitDensity hG model rs pi C hC mu hsq q omega *
    SourcePacket.coefficientMap hG model rs d pi C hC mu hsq v omega g
      ∂SourceMeasure.normalizedOrbitMeasure model a ha hindex mu omega0) = _
  rw [orbitMeasure_eq_standard]
  unfold standardPacket rationalInducedOrbitWavePacket
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  have hd := congrFun (density_eq_standard hG hi hnu I hzeta pi C hC mu hsq q) omega
  have hc := congrArg (fun E => E v omega g)
    (coefficient_eq_standard hG hi hnu I hzeta hK hPK pi C hC mu hsq)
  exact congrArg₂ (fun x y : ℂ => x * y) hd hc

end Source

end Langlands.HarishChandraSchwartz.RationalSemistandard.StandardPacketComparison
