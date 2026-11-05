import Langlands.Global.AdelicSubgroupQuotient
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.GroupScheme.AffinePointClosedImmersion

/-! # Intrinsic Haar measures on actual adelic subgroup rational quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MeasureTheory Set Topology
  TopologicalSpace
open scoped CategoryTheory.MonObj RestrictedProduct ENNReal

namespace Langlands.Global.AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : Langlands.GroupScheme.SubgroupFunctor G)

/-- The actual subgroup principal image is discrete, by its inclusion in the ambient
principal image. No rational descent assertion for an arbitrary subgroup functor is used. -/
theorem isDiscrete_rationalSubgroup :
    IsDiscrete (rationalSubgroup F G U : Set (adelicPoints F G U)) := by
  have hd : IsDiscrete ((fun n : adelicPoints F G U => (n : AdelicGroupPoints F G)) ⁻¹'
      (AdelicGroupPoints.rationalSubgroup F G : Set (AdelicGroupPoints F G))) :=
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F G).preimage
    continuous_subtype_val.continuousOn Subtype.val_injective
  apply hd.mono
  rintro x ⟨q, rfl⟩
  exact ⟨q.val, rfl⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- A represented closed subgroup has closed actual adelic image. -/
theorem isClosed_adelicPoints_range
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] (j : H ⟶ G)
    [IsClosedImmersion j.hom.hom.left] :
    IsClosed (adelicPoints F G (Langlands.GroupScheme.SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G)) := by
  let : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  exact (H.isClosedEmbedding_affinePointsTarget G
    (CommAlgCat.of F (AdeleRing (𝓞 F) F)) j).isClosed_range

instance adelicPointsSecondCountableTopology : SecondCountableTopology (adelicPoints F G U) :=
  secondCountableTopology_induced _ (AdelicGroupPoints F G)
    (fun n : adelicPoints F G U => (n : AdelicGroupPoints F G))

variable [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance subgroupLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

local instance subgroupPolishSpace : PolishSpace (adelicPoints F G U) :=
  hclosed.polishSpace

/-- The actual subgroup quotient's inherited measurable structure is Borel. -/
theorem rationalQuotientBorelSpace : BorelSpace (RationalQuotient F G U) :=
  LeftCosetSpace.discreteQuotientBorelSpace (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U)

local instance quotientBorelSpace : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

/-- The quotient of the actual subgroup Haar measure by its actual principal image. -/
def rationalQuotientHaarMeasure : Measure (RationalQuotient F G U) :=
  LeftCosetSpace.haarQuotientMeasure (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U)

theorem rationalQuotientHaarMeasure_ne_zero :
    rationalQuotientHaarMeasure F G U ≠ 0 :=
  LeftCosetSpace.haarQuotientMeasure_ne_zero (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U)

theorem rationalQuotientHaarMeasure_isLocallyFiniteMeasure :
    IsLocallyFiniteMeasure (rationalQuotientHaarMeasure F G U) :=
  LeftCosetSpace.isLocallyFiniteMeasure_haarQuotientMeasure (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U)

theorem rationalQuotientHaarMeasure_regular :
    (rationalQuotientHaarMeasure F G U).Regular :=
  LeftCosetSpace.regular_haarQuotientMeasure (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U)

/-- Both ambient subgroup Haar and its rational quotient are scaled by this same factor. -/
def quotientMassNormalizer : ℝ≥0∞ :=
  (rationalQuotientHaarMeasure F G U univ)⁻¹

/-- The mass-normalized actual quotient measure. Probability requires compactness below. -/
def normalizedRationalQuotientHaarMeasure : Measure (RationalQuotient F G U) :=
  quotientMassNormalizer F G U • rationalQuotientHaarMeasure F G U

/-- The corresponding normalization of Haar on the actual adelic subgroup. -/
def normalizedHaarMeasure : Measure (adelicPoints F G U) :=
  quotientMassNormalizer F G U • Measure.haar

section Compact

variable [CompactSpace (RationalQuotient F G U)]

theorem rationalQuotientHaarMeasure_isFiniteMeasure :
    IsFiniteMeasure (rationalQuotientHaarMeasure F G U) := by
  let := rationalQuotientHaarMeasure_isLocallyFiniteMeasure F G U
  infer_instance

theorem quotientMassNormalizer_ne_zero : quotientMassNormalizer F G U ≠ 0 := by
  let := rationalQuotientHaarMeasure_isFiniteMeasure F G U
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)

omit [CompactSpace (RationalQuotient F G U)] in
theorem quotientMassNormalizer_ne_top : quotientMassNormalizer F G U ≠ ∞ :=
  ENNReal.inv_ne_top.mpr
    (Measure.measure_univ_ne_zero.mpr (rationalQuotientHaarMeasure_ne_zero F G U))

theorem normalizedRationalQuotientHaarMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (normalizedRationalQuotientHaarMeasure F G U) := by
  let := rationalQuotientHaarMeasure_isFiniteMeasure F G U
  let : NeZero (rationalQuotientHaarMeasure F G U) :=
    ⟨rationalQuotientHaarMeasure_ne_zero F G U⟩
  exact MeasureTheory.isProbabilityMeasureSMul

variable [(Measure.haar : Measure (adelicPoints F G U)).IsMulRightInvariant]

omit [CompactSpace (RationalQuotient F G U)] in
/-- Positive right translation preserves the actual mass-normalized quotient measure.
Analytic right invariance of subgroup Haar remains the explicit premise. -/
theorem measurePreserving_rightTranslate_normalizedRationalQuotientHaarMeasure
    (n : adelicPoints F G U) :
    MeasurePreserving (LeftCosetSpace.rightTranslate (rationalSubgroup F G U) n)
      (normalizedRationalQuotientHaarMeasure F G U)
      (normalizedRationalQuotientHaarMeasure F G U) :=
  (LeftCosetSpace.measurePreserving_rightTranslate_haarQuotientMeasure
    (rationalSubgroup F G U) (isDiscrete_rationalSubgroup F G U) n).smul_measure _

/-- The normalized ambient Haar and normalized quotient have the same exact counting-measure
Weil formula. No algebraic determinant is substituted for an analytic Haar modulus. -/
theorem normalizedRationalQuotientHaarMeasure_isCompatible :
    Langlands.QuotientIntegration.IsCompatible (rationalSubgroup F G U)
      (normalizedHaarMeasure F G U) Measure.count
      (normalizedRationalQuotientHaarMeasure F G U) := by
  let : (rationalQuotientHaarMeasure F G U).Regular :=
    rationalQuotientHaarMeasure_regular F G U
  let := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  have hbase := LeftCosetSpace.haarQuotientMeasure_isCompatible
    (rationalSubgroup F G U) (isDiscrete_rationalSubgroup F G U)
  refine
    { nonzero := NeZero.ne _
      regular := Measure.Regular.smul (quotientMassNormalizer_ne_top F G U)
      right_invariant := measurePreserving_rightTranslate_normalizedRationalQuotientHaarMeasure
        F G U
      averaging_integrable := fun f hf hs =>
        (hbase.averaging_integrable f hf hs).smul_measure
          (quotientMassNormalizer_ne_top F G U)
      integral_formula := ?_ }
  intro f hf hs
  change (∫ q, Langlands.QuotientIntegration.quotientAverage
      (rationalSubgroup F G U) Measure.count f q
        ∂(quotientMassNormalizer F G U • rationalQuotientHaarMeasure F G U)) =
    ∫ n, f n ∂(quotientMassNormalizer F G U • Measure.haar)
  rw [integral_smul_measure, integral_smul_measure]
  exact congrArg (fun z : ℂ => (quotientMassNormalizer F G U).toReal • z)
    (hbase.integral_formula f hf hs)

end Compact

end Langlands.Global.AdelicSubgroupPoints
