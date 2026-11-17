import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardStandardPacketComparison
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

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.StandardFormComparison

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

open StandardPacketComparison

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
  (a : A.toGrp ⟶ (model).scheme) (ha : IsSplitComponent a)
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  [nC : ((model).splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
  [mC : MeasurableSpace (M ⧸ (model).splitCenter a)] [bC : BorelSpace (M ⧸ (model).splitCenter a)]
  (mu : Measure (M ⧸ (model).splitCenter a)) [hm : mu.IsHaarMeasure] [hinv : mu.IsInvInvariant]
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
set_option hygiene false in
local notation "chi" => CommGroupScheme.groupHom zeta ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom zeta ≫ i)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom zeta ≫ i) hG
set_option hygiene false in
local notation "jP" => standardScalar hG hi hnu I hzeta pi q
set_option hygiene false in
local notation "rho" => standardCharacterHaar hG hi hnu I a ha hindex

local instance sourceHaarFinite : IsFiniteMeasure rho := by
  change IsFiniteMeasure (SourceMeasure.unitaryCharacterHaar model a ha hindex)
  infer_instance

local instance sourceHaarOpenPos : (rho).IsOpenPosMeasure := by
  change (SourceMeasure.unitaryCharacterHaar model a ha hindex).IsOpenPosMeasure
  infer_instance

variable [fQ : Finite (M ⧸ (commonNormKernel (model).normCharacters ⊔ C))]
  (hj : jP ≠ 0)
  (hnn : ∀ z : unitaryUnramifiedCharacters
      (fun psi => (rationalNormCharacters MS psi).toMul),
    RationalFunctionNonnegAt MS (parameterProjection_continuous chi) hMS (jP)⁻¹
      (unitaryToUnramified MS z))

set_option maxHeartbeats 1800000 in
/-- The published standard product core at the actual source measures and scalar data. -/
@[instance_reducible]
def standardCore :=
  let hirr := standard_irreducible hG hi hnu I hzeta pi q
  let hreg := standard_inverseRegular hG hi hnu I hzeta pi q
  @standardLeviPlancherelOrbitProductCore F _ _ _ _ S G _ _ i nu hG hi hnu I zeta hzeta pi C
    (show (show Subgroup OldM from C).Normal from nC) hC
    (show MeasurableSpace (OldM ⧸ C) from mC)
    (show Measure (OldM ⧸ C) from mu)
    (show (show Measure (OldM ⧸ C) from mu).IsHaarMeasure from hm) hsq
    q.reflection q.centralCharacters q.compact q.isCompact q.factorization q.oppositeFactorization
    q.forward q.reverse q.forwardDomain q.reverseDomain q.forwardOpen q.forwardNonempty q.forwardContained
    q.reverseOpen q.reverseNonempty q.reverseContained q.irreducibleDomain
    q.irreducibleOpen q.irreducibleNonempty hirr
    (show BorelSpace (OldM ⧸ C) from bC)
    (show (show Measure (OldM ⧸ C) from mu).IsInvInvariant from hinv)
    K hK hPK
    (show Finite (discreteSeriesStabilizer C hC mu nuM omega0) from
      SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0)
    (show Finite (OldM ⧸ (commonNormKernel nuM ⊔ C)) from fQ)
    rho (show IsFiniteMeasure rho from inferInstance)
    (show (rho).IsOpenPosMeasure from inferInstance) hreg hj hnn

set_option maxHeartbeats 1800000 in
/-- The actual inverse-degree source integral is the published standard product-core inner product. -/
theorem weightedOrbitForm_eq_standardCore_inner (v w : smoothOrbitSections model d pi) :
    SourceForm.weightedOrbitForm hG model rs d a ha hindex mu pi hsq q v w =
      (standardCore hG hi hnu I hzeta hK hPK a ha hindex mu pi hsq q hj hnn).inner v w := by
  let hirr := standard_irreducible hG hi hnu I hzeta pi q
  let hreg := standard_inverseRegular hG hi hnu I hzeta pi q
  have h := @standardLeviPlancherelOrbitProductCore_inner F _ _ _ _ S G _ _ i nu hG hi hnu I zeta hzeta pi C
    (show (show Subgroup OldM from C).Normal from nC) hC
    (show MeasurableSpace (OldM ⧸ C) from mC)
    (show Measure (OldM ⧸ C) from mu)
    (show (show Measure (OldM ⧸ C) from mu).IsHaarMeasure from hm) hsq
    q.reflection q.centralCharacters q.compact q.isCompact q.factorization q.oppositeFactorization
    q.forward q.reverse q.forwardDomain q.reverseDomain q.forwardOpen q.forwardNonempty q.forwardContained
    q.reverseOpen q.reverseNonempty q.reverseContained q.irreducibleDomain
    q.irreducibleOpen q.irreducibleNonempty hirr
    (show BorelSpace (OldM ⧸ C) from bC)
    (show (show Measure (OldM ⧸ C) from mu).IsInvInvariant from hinv)
    K hK hPK
    (show Finite (discreteSeriesStabilizer C hC mu nuM omega0) from
      SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0)
    (show Finite (OldM ⧸ (commonNormKernel nuM ⊔ C)) from fQ)
    rho (show IsFiniteMeasure rho from inferInstance)
    (show (rho).IsOpenPosMeasure from inferInstance) hreg hj hnn v w
  let := SourceMeasure.finite_literalDiscreteSeriesStabilizer model a ha hindex mu omega0
  unfold SourceForm.weightedOrbitForm
  rw [orbitMeasure_eq_standard]
  calc
    _ = ∫ omega, standardDensity hG hi hnu I hzeta pi C hC mu hsq q omega *
        SourceForm.pairing hG model rs d pi C hC mu hsq v w omega
          ∂discreteSeriesOrbitMeasure (model).normCharacters C hC mu omega0 rho := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      exact congrArg (fun x => x * SourceForm.pairing hG model rs d pi C hC mu hsq v w omega)
        (congrFun (density_eq_standard hG hi hnu I hzeta pi C hC mu hsq q) omega)
    _ = _ := by
      convert h.symm using 1; rfl

end Langlands.HarishChandraSchwartz.RationalSemistandard.StandardFormComparison
