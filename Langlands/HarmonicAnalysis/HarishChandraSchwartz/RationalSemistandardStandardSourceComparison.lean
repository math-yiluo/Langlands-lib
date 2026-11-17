import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
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

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.StandardSourceComparison

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
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu) (I : Finset (RationalPointFamily.SimpleRoot i nu))
  {zeta : cocharacterLattice S}
  (hzeta : IsStandardCocharacter i nu (RationalPointFamily.rootSet i nu I) zeta)

/-- The exact published standard triple has its actual cocharacter presentation. -/
abbrev presentation : CocharacterPresentation hG (standardIndex hG hi hnu I) :=
  ⟨zeta, (SemistandardSpectralIndex.ofStandard_eq_ofCocharacter hG hi nu hnu
    (RationalPointFamily.rootSet i nu I) (RationalPointFamily.rootSet_subset i nu I) zeta hzeta).symm⟩

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

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Both literal group identifications fix the original ambient rational points. -/
theorem literalHomeomorph_eq : (rs).literalLeviHomeomorph =
    standardLeviDynamicHomeomorph hG hi hnu I hzeta := rfl

/-- The actual character restriction equals the existing standard restriction. -/
theorem characterRestrict_eq : SourceDensity.characterRestrict model rs =
    standardLeviCharacterRestrict hG hi hnu I hzeta := by
  apply ContinuousMonoidHom.ext
  intro z
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro m
  rw [SourceDensity.characterRestrict_apply]
  convert (standardLeviCharacterRestrict_apply hG hi hnu I hzeta z m).symm using 1; rfl

variable (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))
  (C : Subgroup M) [nC : C.Normal] (hC : C ≤ Subgroup.center M)
  [mC : MeasurableSpace (M ⧸ C)] (mu : Measure (M ⧸ C)) [hm : mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation mu)
  (q : OrbitPacketData rs pi)

/-- The primitive generic irreducibility input uses the identical literal pullback. -/
theorem standard_irreducible : ∀ z ∈ q.irreducibleDomain,
    (UnramifiedLeviInduction
      (DynamicOppositeStandardIntertwining.decomposition (CommGroupScheme.groupHom zeta ≫ i))
      (radical_isClosed (CommGroupScheme.groupHom zeta ≫ i))
      (leviNormCharacters (CommGroupScheme.groupHom zeta ≫ i))
      (parameterTransport (CommGroupScheme.groupHom zeta ≫ i) z)
      (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hnu I hzeta) pi.obj)).IsIrreducible := by
  rw [← literalHomeomorph_eq hG hi hnu I hzeta]
  exact q.irreducible

/-- The actual canonical scalar in the published standard presentation. -/
abbrev standardScalar :=
  conditionalCanonicalRationalScalar (CommGroupScheme.groupHom zeta ≫ i)
    q.reflection q.centralCharacters hG q.compact q.isCompact q.factorization q.oppositeFactorization
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hnu I hzeta) pi.obj)
    q.forward q.reverse q.forwardNonempty q.forwardContained q.reverseNonempty q.reverseContained
    q.irreducibleNonempty (standard_irreducible hG hi hnu I hzeta pi q)

/-- No scalar is reselected when the standard point-group presentation is used. -/
theorem scalar_eq : standardScalar hG hi hnu I hzeta pi q =
    conditionalCanonicalRationalScalar (CommGroupScheme.groupHom (rs).cocharacter ≫ i)
      q.reflection q.centralCharacters hG q.compact q.isCompact q.factorization q.oppositeFactorization
      (SmoothRep.pullback (rs).literalLeviHomeomorph pi.obj)
      q.forward q.reverse q.forwardNonempty q.forwardContained q.reverseNonempty q.reverseContained
      q.irreducibleNonempty q.irreducible := by
  rfl

/-- The original inverse-regularity input transports along equality of the actual scalar. -/
theorem standard_inverseRegular : RationalFunctionUnitaryRegular
    (parameterScheme (CommGroupScheme.groupHom zeta ≫ i))
    (parameterScheme_isConnectedReductive (CommGroupScheme.groupHom zeta ≫ i) hG)
    (standardScalar hG hi hnu I hzeta pi q)⁻¹ := by
  rw [scalar_eq hG hi hnu I hzeta pi q]
  exact q.inverseRegular

set_option maxHeartbeats 1800000 in
/-- The published standard density at exactly the same primitive scalar data. -/
def standardDensity :=
  let hirr := standard_irreducible hG hi hnu I hzeta pi q
  let hreg := standard_inverseRegular hG hi hnu I hzeta pi q
  @standardLeviPlancherelWeight F _ _ _ _ S G _ _ i nu hG hi hnu I zeta hzeta pi C
    (show (show Subgroup OldM from C).Normal from nC) hC
    (show MeasurableSpace (OldM ⧸ C) from mC)
    (show Measure (OldM ⧸ C) from mu)
    (show (show Measure (OldM ⧸ C) from mu).IsHaarMeasure from hm) hsq
    q.reflection q.centralCharacters q.compact q.isCompact q.factorization q.oppositeFactorization
    q.forward q.reverse q.forwardDomain q.reverseDomain q.forwardOpen q.forwardNonempty q.forwardContained
    q.reverseOpen q.reverseNonempty q.reverseContained q.irreducibleDomain
    q.irreducibleOpen q.irreducibleNonempty
    hirr hreg

set_option maxHeartbeats 1800000 in
/-- The actual semistandard orbit density restricts to the published standard density. -/
theorem density_eq_standard : SourceForm.orbitDensity hG model rs pi C hC mu hsq q =
    standardDensity hG hi hnu I hzeta pi C hC mu hsq q := by
  funext omega
  obtain ⟨z, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu (model).normCharacters
    (discreteSeriesClass C hC mu pi hsq)).surjective omega
  have h := @standardLeviPlancherelWeight_orbitMap F _ _ _ _ S G _ _ i nu hG hi hnu I zeta hzeta pi C
    (show (show Subgroup OldM from C).Normal from nC) hC
    (show MeasurableSpace (OldM ⧸ C) from mC)
    (show Measure (OldM ⧸ C) from mu)
    (show (show Measure (OldM ⧸ C) from mu).IsHaarMeasure from hm) hsq
    q.reflection q.centralCharacters q.compact q.isCompact q.factorization q.oppositeFactorization
    q.forward q.reverse q.forwardDomain q.reverseDomain q.forwardOpen q.forwardNonempty q.forwardContained
    q.reverseOpen q.reverseNonempty q.reverseContained q.irreducibleDomain
    q.irreducibleOpen q.irreducibleNonempty
    (standard_irreducible hG hi hnu I hzeta pi q)
    (standard_inverseRegular hG hi hnu I hzeta pi q) z
  unfold SourceForm.orbitDensity
  rw [SourceDensity.orbitPlancherelWeight_orbitMap]
  convert h.symm using 1
  · congr 1
    exact congrArg (fun f => f z) (characterRestrict_eq hG hi hnu I hzeta)
  · rfl

end Langlands.HarishChandraSchwartz.RationalSemistandard.StandardSourceComparison
