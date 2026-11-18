import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceFormalDegree

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

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceRepresentativeComparison

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
  SourceMeasure.modelAffineHom SourceMeasure.modelAffine SourceMeasure.modelSmooth
  SourceMeasure.modelFiniteType SourceMeasure.modelTopology SourceMeasure.modelNonarchimedean

attribute [local instance]
  SourceMeasure.intrinsicQuotientMeasurable SourceMeasure.intrinsicQuotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} (hG : IsConnectedReductive G)
  (model : LeviModel p) (r : CocharacterPresentation hG p) (d : CompactData p)

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
  (a : A.toGrp ⟶ model.scheme) (ha : IsSplitComponent a)
  (hindex : (RenardCartan.splitValuationImage a).FiniteIndex)
  [(model.splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
  [MeasurableSpace (levi p ⧸ model.splitCenter a)] [BorelSpace (levi p ⧸ model.splitCenter a)]
  (mu : Measure (levi p ⧸ model.splitCenter a)) [mu.IsHaarMeasure] [mu.IsInvInvariant]

set_option hygiene false in
local notation "C" => model.splitCenter a
set_option hygiene false in
local notation "hC" => model.splitCenter_le_center a ha

section Recenter

variable (O : OrbitClass.{u, uV} model a ha mu)
  (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (hsq' : IsSquareIntegrableModCentralSubgroup C hC pi'.obj.representation mu)
  (hO : (Quotient.mk _ (discreteSeriesClass C hC mu pi' hsq') : OrbitClass model a ha mu) = O)

set_option hygiene false in
local notation "pi0" => orbitRepresentative model a ha mu O
set_option hygiene false in
local notation "hsq0" => orbitRepresentative_isSquareIntegrable model a ha mu O
set_option hygiene false in
local notation "changeBase" => orbitSmoothSectionsBaseEquiv model a ha mu d O pi' hsq' hO
set_option hygiene false in
local notation "repChange" => unitaryOrbitRepresentativeBaseEquiv model.normCharacters pi0
  (orbitRepresentativeMember model a ha mu O pi' hsq' hO)

omit [IsAffine A.X.left] [(rationalPoints.map a).range.Normal] in
include hO in
/-- Recentring the actual orbit retains the source Schur degree. -/
theorem degree_recentered :
    representationFormalDegree C hC mu (compactOpenCofinal_levi model d) hsq' pi'.property.1 =
      representationFormalDegree C hC mu (compactOpenCofinal_levi model d) hsq0 (pi0).property.1 :=
  (SourceDegree.orbitDegree_eq_representationDegree model d a ha mu O pi' hsq' hO).symm.trans
    (SourceDegree.orbitDegree_eq_representationDegree model d a ha mu O pi0 hsq0
      (mk_discreteSeriesClass_orbitRepresentative model a ha mu O))

omit [IsAffine A.X.left] [(rationalPoints.map a).range.Normal]
  [BorelSpace (levi p ⧸ C)] [mu.IsInvInvariant] in
/-- The actual coefficient agrees at every unchanged inducing object after recentering. -/
theorem coefficient_recentered (v : smoothOrbitSections model d pi0)
    (B : UnitaryOrbitRepresentative model.normCharacters pi0) :
    SourcePacket.coefficientMap hG model r d pi' C hC mu hsq' (changeBase v)
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit model.normCharacters pi' C hC mu hsq'
        (repChange B)) =
    SourcePacket.coefficientMap hG model r d pi0 C hC mu hsq0 v
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit model.normCharacters pi0 C hC mu hsq0 B) := by
  have h := SourcePacket.coefficientMap_representative hG model r d pi' C hC mu hsq'
    (changeBase v) (repChange B)
  have h0 := SourcePacket.coefficientMap_representative hG model r d pi0 C hC mu hsq0 v B
  exact h.trans h0.symm

omit [IsAffine A.X.left] [(rationalPoints.map a).range.Normal] in
/-- The actual inverse-degree pairing agrees under the identical representative reindexing. -/
theorem pairing_recentered (v w : smoothOrbitSections model d pi0)
    (B : UnitaryOrbitRepresentative model.normCharacters pi0) :
    SourceForm.pairing hG model r d pi' C hC mu hsq' (changeBase v) (changeBase w)
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit model.normCharacters pi' C hC mu hsq'
        (repChange B)) =
    SourceForm.pairing hG model r d pi0 C hC mu hsq0 v w
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit model.normCharacters pi0 C hC mu hsq0 B) := by
  have h := SourceForm.pairing_representative hG model r d pi' C hC mu hsq'
    (changeBase v) (changeBase w) (repChange B)
  have h0 := SourceForm.pairing_representative hG model r d pi0 C hC mu hsq0 v w B
  exact h.trans h0.symm

end Recenter

/-- Exact remaining representative-independence of the actual source integrals.
The coefficient/degree/pairing maps are already fixed and compared above. -/
def RepresentativeSourceComparisonStatement : Prop :=
  IsMaximalSplitTorus i →
  ∀ (nu : cocharacterLattice S), IsGenericCocharacter i nu →
    ∀ (K0 : OpenSubgroup (rationalPoints G)) (_hK0 : IsCompact (K0 : Set (rationalPoints G))),
      BruhatTits.SpecialCompact.SpecialCompactProperties F i nu
        (K0 : Subgroup (rationalPoints G)) → d.compact = K0 →
      ∀ (O : OrbitClass.{u, uV} model a ha mu)
        (pi' : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
        (hsq' : IsSquareIntegrableModCentralSubgroup C hC pi'.obj.representation mu)
        (hO : (Quotient.mk _ (discreteSeriesClass C hC mu pi' hsq') : OrbitClass model a ha mu) = O)
        (q0 : OrbitPacketData r (orbitRepresentative model a ha mu O))
        (q1 : OrbitPacketData r pi'),
        q0.compact = K0 → q1.compact = K0 →
        ∀ (v w : smoothOrbitSections model d (orbitRepresentative model a ha mu O)),
          q1.packetLinear model d a ha hindex mu hsq'
              (orbitSmoothSectionsBaseEquiv model a ha mu d O pi' hsq' hO v) =
            q0.packetLinear model d a ha hindex mu
              (orbitRepresentative_isSquareIntegrable model a ha mu O) v ∧
          SourceForm.weightedOrbitForm hG model r d a ha hindex mu pi' hsq' q1
              (orbitSmoothSectionsBaseEquiv model a ha mu d O pi' hsq' hO v)
              (orbitSmoothSectionsBaseEquiv model a ha mu d O pi' hsq' hO w) =
            SourceForm.weightedOrbitForm hG model r d a ha hindex mu
              (orbitRepresentative model a ha mu O)
              (orbitRepresentative_isSquareIntegrable model a ha mu O) q0 v w

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceRepresentativeComparison
