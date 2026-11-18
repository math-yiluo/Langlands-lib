import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm
import Langlands.Representation.Plancherel.DiscreteSeriesFormalDegree

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

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDegree

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
  {p : SemistandardSpectralIndex i} (model : LeviModel p) (d : CompactData p)

include d in
/-- The actual model point group inherits compact-open cofinality through its inclusion. -/
theorem intrinsicCompactOpenCofinal : CompactOpenCofinal (rationalPoints model.scheme) := by
  intro K
  let L := K.comap model.pointHomeomorph.symm.toMulEquiv.toMonoidHom
    model.pointHomeomorph.symm.continuous
  obtain ⟨N, hN, hNL⟩ := compactOpenCofinal_levi model d L
  refine ⟨N.comap model.pointHomeomorph.toMulEquiv.toMonoidHom
    model.pointHomeomorph.continuous, ?_, ?_⟩
  · exact model.pointHomeomorph.toHomeomorph.isClosedEmbedding.isCompact_preimage hN
  · intro x hx
    have h := hNL hx
    change model.pointHomeomorph.symm (model.pointHomeomorph x) ∈ K at h
    simpa only [ContinuousMulEquiv.symm_apply_apply] using h

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left]
  (a : A.toGrp ⟶ model.scheme) (ha : IsSplitComponent a)
  [(model.splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
  [MeasurableSpace (levi p ⧸ model.splitCenter a)] [BorelSpace (levi p ⧸ model.splitCenter a)]
  (mu : Measure (levi p ⧸ model.splitCenter a)) [mu.IsHaarMeasure] [mu.IsInvInvariant]

set_option hygiene false in
local notation "C" => model.splitCenter a
set_option hygiene false in
local notation "hC" => model.splitCenter_le_center a ha
set_option hygiene false in
local notation "CL" => (rationalPoints.map a).range
set_option hygiene false in
local notation "hCL" => ha.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "muL" => SourceMeasure.intrinsicQuotientHaar model a mu

/-- The actual pullback quotient Haar preserves the displayed inversion invariance. -/
instance intrinsicInverseInvariant : (muL).IsInvInvariant := by
  let e := SourceMeasure.centralQuotientHomeomorph model a
  constructor
  change Measure.map Inv.inv (Measure.map e.symm mu) = Measure.map e.symm mu
  have he : Measurable (fun x => e.symm x) := e.symm.continuous.measurable
  have hc : Inv.inv ∘ (fun x => e.symm x) = (fun x => e.symm x) ∘ Inv.inv := by
    funext x
    exact (map_inv e.symm x).symm
  calc
    _ = Measure.map (Inv.inv ∘ (fun x => e.symm x)) mu := Measure.map_map measurable_inv he
    _ = Measure.map ((fun x => e.symm x) ∘ Inv.inv) mu := congrArg (fun f => Measure.map f mu) hc
    _ = Measure.map (fun x => e.symm x) (Measure.map Inv.inv mu) :=
      (Measure.map_map he measurable_inv).symm
    _ = _ := congrArg (fun v => Measure.map (fun x => e.symm x) v) (Measure.map_inv_eq_self mu)

/-- The actual source Schur degree, descended to the existing unitary twist-orbit class. -/
def orbitDegree (O : OrbitClass model a ha mu) : ℝ :=
  discreteSeriesOrbitFormalDegree C hC mu (compactOpenCofinal_levi model d) model.normCharacters O

omit [IsAffine A.X.left] [(rationalPoints.map a).range.Normal] in
theorem orbitDegree_pos (O : OrbitClass model a ha mu) : 0 < orbitDegree model d a ha mu O :=
  discreteSeriesOrbitFormalDegree_pos C hC mu (compactOpenCofinal_levi model d) model.normCharacters O

omit [IsAffine A.X.left] [(rationalPoints.map a).range.Normal] in
/-- Every actual inducing representative gives this same source degree. -/
theorem orbitDegree_eq_representationDegree (O : OrbitClass model a ha mu)
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (hsq : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation mu)
    (hO : (Quotient.mk _ (discreteSeriesClass C hC mu pi hsq) : OrbitClass model a ha mu) = O) :
    orbitDegree model d a ha mu O =
      representationFormalDegree C hC mu (compactOpenCofinal_levi model d) hsq pi.property.1 := by
  rw [← hO]
  exact discreteSeriesFormalDegree_mk C hC mu (compactOpenCofinal_levi model d) pi hsq

/-- Exact remaining source formal-degree transport along the actual model inclusion.
Both quotients, the pulled-back Haar and the inducing class are prescribed constructions. -/
def FormalDegreeTransportStatement : Prop :=
  ∀ omega : DiscreteSeriesClass.{u, uV} C hC mu,
    discreteSeriesFormalDegree C hC mu (compactOpenCofinal_levi model d) omega =
      discreteSeriesFormalDegree CL hCL muL (intrinsicCompactOpenCofinal model d)
        (SourceMeasure.intrinsicDiscreteSeriesClass model a ha mu omega)

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDegree
