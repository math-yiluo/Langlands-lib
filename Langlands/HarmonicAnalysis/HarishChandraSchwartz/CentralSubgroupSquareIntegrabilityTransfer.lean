import Langlands.Representation.Unitary.CentralSubgroupForm
import Langlands.Representation.Plancherel.CentralSubgroupComparisonProof
import Langlands.Representation.Plancherel.RationalModerateGrowthUniformization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecayProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness

/-! # Square-integrability transfer between central quotients -/

noncomputable section

open MeasureTheory

namespace Langlands.Plancherel

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (C : Subgroup G) [C.Normal] (hC : C ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ C)]
  [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- The pushforward of the displayed central-quotient measure to the full
central quotient; no normalization or arbitrary measure choice is inserted. -/
def centralSubgroupFullQuotientMeasure (muC : Measure (G ⧸ C)) :
    Measure (G ⧸ Subgroup.center G) :=
  muC.map (centralQuotientProjection C hC)

variable [BorelSpace (G ⧸ C)] [BorelSpace (G ⧸ Subgroup.center G)]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

omit [T2Space G] in
/-- A nonzero irreducible square-integrable representation makes the actual
pushforward to the full center a Haar measure, even when C is not closed. -/
theorem centralSubgroupFullQuotientMeasure_isHaar (hcofinal : CompactOpenCofinal G)
    (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (muC : Measure (G ⧸ C)) [muC.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ muC) :
    (centralSubgroupFullQuotientMeasure C hC muC).IsHaarMeasure := by
  classical
  obtain ⟨hadm, c, hL2⟩ := hsq
  obtain ⟨ℓ, hℓ⟩ := exists_nonzero_smoothDual_of_irreducible_compact_cofinal
    hcofinal ρ hadm.1 hirr
  obtain ⟨v, hv⟩ : ∃ v, ℓ.val v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    ext v
    exact hn v
  exact centralQuotientProjection_map_isHaarMeasure C hC c hadm.1 ℓ.val v hv muC (hL2 ℓ v)

omit [T2Space G] in
/-- All original smooth-dual coefficients remain square integrable for the
actual pushed-forward full-center Haar measure. -/
theorem isSquareIntegrableModCenter_fullQuotientMeasure (hcofinal : CompactOpenCofinal G)
    (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (muC : Measure (G ⧸ C)) [muC.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ muC) :
    letI := centralSubgroupFullQuotientMeasure_isHaar C hC hcofinal ρ hirr muC hsq
    IsSquareIntegrableModCenter ρ (centralSubgroupFullQuotientMeasure C hC muC) := by
  let := centralSubgroupFullQuotientMeasure_isHaar C hC hcofinal ρ hirr muC hsq
  obtain ⟨hadm, c, hL2⟩ := hsq
  exact ⟨hadm, c, fun ℓ v => centralSubgroupCoefficientNorm_memLp_map C hC c hadm.1 ℓ.val v muC (hL2 ℓ v)⟩

/-- Square integrability modulo arbitrary C transfers to any closed central A
whose quotient in the full center is compact, for every displayed Haar measure
on G/A. There is no containment premise between C and A. -/
theorem isSquareIntegrableModCentralSubgroup_transfer
    (hcofinal : CompactOpenCofinal G) (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (muC : Measure (G ⧸ C)) [muC.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC ρ muC)
    (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G) (hAc : IsClosed (A : Set G))
    [CompactSpace (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G))]
    [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
    (muA : Measure (G ⧸ A)) [muA.IsHaarMeasure] :
    IsSquareIntegrableModCentralSubgroup A hA ρ muA := by
  let muZ := centralSubgroupFullQuotientMeasure C hC muC
  have : muZ.IsHaarMeasure := centralSubgroupFullQuotientMeasure_isHaar C hC hcofinal ρ hirr muC hsq
  have hZ : IsSquareIntegrableModCenter ρ muZ :=
    isSquareIntegrableModCenter_fullQuotientMeasure C hC hcofinal ρ hirr muC hsq
  exact ((centralSubgroupCoefficientLpComparison G A hA hAc muA muZ V ρ).2).mpr hZ

end Langlands.Plancherel

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- On actual rational points, arbitrary Borel-compatible central-subgroup
square integrability transfers to the actual split-component quotient for any
of its Haar measures; no valuation-index hypothesis is needed. -/
theorem isSquareIntegrable_splitComponent_of_centralSubgroup (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
    (C : Subgroup (rationalPoints G)) [C.Normal] (hC : C ≤ Subgroup.center (rationalPoints G))
    [MeasurableSpace (rationalPoints G ⧸ C)] [BorelSpace (rationalPoints G ⧸ C)]
    (muC : Measure (rationalPoints G ⧸ C)) [muC.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation muC)
    [(rationalPoints.map s).range.Normal]
    [MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range)]
    [BorelSpace (rationalPoints G ⧸ (rationalPoints.map s).range)]
    (muA : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [muA.IsHaarMeasure] :
    IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
      hs.isCentralSplitTorus.isCentral.range_le_center π.obj.representation muA := by
  let : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : MeasurableSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) := borel _
  let : BorelSpace (rationalPoints G ⧸ Subgroup.center (rationalPoints G)) := ⟨rfl⟩
  let := compactSpace_center_quotient_splitComponent hG hs
  exact isSquareIntegrableModCentralSubgroup_transfer C hC (rationalPoint_compactOpenCofinal F G)
    π.obj.representation π.property.1 muC hsq (rationalPoints.map s).range
    hs.isCentralSplitTorus.isCentral.range_le_center (isClosed_range_splitComponent G s hs) muA

end Langlands.HarishChandraSchwartz
