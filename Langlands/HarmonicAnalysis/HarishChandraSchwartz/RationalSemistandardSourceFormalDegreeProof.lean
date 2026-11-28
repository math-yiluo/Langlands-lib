import Langlands.Representation.Plancherel.FormalDegreePullbackProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceFormalDegree

/-! # Formal degree transport to the actual semistandard Levi model -/

noncomputable section

universe u uV uG uH

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
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
  SourceMeasure.intrinsicQuotientMeasurable SourceMeasure.intrinsicQuotientBorel

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
/-- Schur degrees agree under the actual model identification with the prescribed quotient Haar. -/
theorem formalDegreeTransport
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
    {p : SemistandardSpectralIndex i} (model : LeviModel p) (d : CompactData p)
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ model.scheme) (ha : IsSplitComponent a)
    [(model.splitCenter a).Normal] [(rationalPoints.map a).range.Normal]
    [MeasurableSpace (levi p ⧸ model.splitCenter a)] [BorelSpace (levi p ⧸ model.splitCenter a)]
    (mu : Measure (levi p ⧸ model.splitCenter a)) [mu.IsHaarMeasure] [mu.IsInvInvariant] :
    FormalDegreeTransportStatement.{u, uV} model d a ha mu := by
  intro ω
  rcases ω with ⟨ω, hω⟩
  induction ω using Quotient.inductionOn with
  | h π =>
    let C := model.splitCenter a
    let hC := model.splitCenter_le_center a ha
    let CL := (rationalPoints.map a).range
    let hCL := ha.isCentralSplitTorus.isCentral.range_le_center
    let muL := SourceMeasure.intrinsicQuotientHaar model a mu
    let πL := IrreducibleAdmissibleRep.pullback model.pointHomeomorph π
    let hmap := SourceMeasure.map_intrinsicQuotientHaar model a mu
    have hπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu := hω
    have hπL : IsSquareIntegrableModCentralSubgroup CL hCL πL.obj.representation muL :=
      (isSquareIntegrableModCentralSubgroup_comp_iff model.pointHomeomorph C hC CL hCL
        rfl mu muL hmap π.obj.representation).mpr hπ
    change discreteSeriesFormalDegree C hC mu (compactOpenCofinal_levi model d)
        (discreteSeriesClass C hC mu π hπ) =
      discreteSeriesFormalDegree CL hCL muL (intrinsicCompactOpenCofinal model d)
        (discreteSeriesClass CL hCL muL πL hπL)
    calc
      _ = representationFormalDegree C hC mu (compactOpenCofinal_levi model d)
            hπ π.property.1 :=
        discreteSeriesFormalDegree_mk C hC mu (compactOpenCofinal_levi model d) π hπ
      _ = representationFormalDegree CL hCL muL (intrinsicCompactOpenCofinal model d)
            hπL πL.property.1 :=
        Langlands.Plancherel.representationFormalDegree_pullback model.pointHomeomorph C hC CL hCL rfl
          mu muL hmap (compactOpenCofinal_levi model d) (intrinsicCompactOpenCofinal model d)
          hπ π.property.1 hπL πL.property.1
      _ = _ :=
        (discreteSeriesFormalDegree_mk CL hCL muL (intrinsicCompactOpenCofinal model d) πL hπL).symm

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDegree
