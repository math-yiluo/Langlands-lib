import Langlands.Global.AdelicGroupPolish
import Langlands.Global.LeftCosetWeilMeasure

/-! # Haar measures on actual rational adelic quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MeasureTheory Set Topology
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The Borel sigma algebra of the existing full adelic point topology. -/
instance measurableSpace : MeasurableSpace (AdelicGroupPoints F G) :=
  borel (AdelicGroupPoints F G)

instance borelSpace : BorelSpace (AdelicGroupPoints F G) := ⟨rfl⟩

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Discreteness of the actual principal subgroup in the full adelic group. -/
theorem isDiscrete_rationalSubgroup :
    IsDiscrete (rationalSubgroup F G : Set (AdelicGroupPoints F G)) :=
  SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance

/-- Discreteness of the actual principal subgroup in the norm-one group. -/
theorem isDiscrete_rationalNormOneSubgroup :
    IsDiscrete (rationalNormOneSubgroup F G : Set (normOneSubgroup F G)) :=
  SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance

/-- The inherited quotient measurable structure agrees with the quotient Borel structure. -/
instance rationalQuotientBorelSpace : BorelSpace (RationalQuotient F G) :=
  LeftCosetSpace.discreteQuotientBorelSpace (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G)

/-- The norm-one quotient also retains its inherited quotient measurable structure. -/
instance normOneRationalQuotientBorelSpace : BorelSpace (NormOneRationalQuotient F G) :=
  LeftCosetSpace.discreteQuotientBorelSpace (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G)

/-- The explicit quotient of the actual full adelic Haar measure by principal points. -/
def rationalQuotientHaarMeasure : Measure (RationalQuotient F G) :=
  LeftCosetSpace.haarQuotientMeasure (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G)

/-- The explicit quotient of the actual norm-one Haar measure by principal points. -/
def normOneRationalQuotientHaarMeasure : Measure (NormOneRationalQuotient F G) :=
  LeftCosetSpace.haarQuotientMeasure (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G)

theorem rationalQuotientHaarMeasure_ne_zero : rationalQuotientHaarMeasure F G ≠ 0 :=
  LeftCosetSpace.haarQuotientMeasure_ne_zero (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G)

theorem normOneRationalQuotientHaarMeasure_ne_zero :
    normOneRationalQuotientHaarMeasure F G ≠ 0 :=
  LeftCosetSpace.haarQuotientMeasure_ne_zero (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G)

instance rationalQuotientHaarMeasure_isLocallyFiniteMeasure :
    IsLocallyFiniteMeasure (rationalQuotientHaarMeasure F G) :=
  LeftCosetSpace.isLocallyFiniteMeasure_haarQuotientMeasure (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G)

instance normOneRationalQuotientHaarMeasure_isLocallyFiniteMeasure :
    IsLocallyFiniteMeasure (normOneRationalQuotientHaarMeasure F G) :=
  LeftCosetSpace.isLocallyFiniteMeasure_haarQuotientMeasure (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G)

instance rationalQuotientHaarMeasure_regular :
    (rationalQuotientHaarMeasure F G).Regular :=
  LeftCosetSpace.regular_haarQuotientMeasure (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G)

instance normOneRationalQuotientHaarMeasure_regular :
    (normOneRationalQuotientHaarMeasure F G).Regular :=
  LeftCosetSpace.regular_haarQuotientMeasure (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G)

/-- Any actual fundamental domain gives the same full rational quotient measure. -/
theorem rationalQuotientHaarMeasure_eq {s : Set (AdelicGroupPoints F G)}
    (hs : IsFundamentalDomain (rationalSubgroup F G) s Measure.haar) :
    rationalQuotientHaarMeasure F G =
      LeftCosetSpace.quotientMeasure (rationalSubgroup F G) Measure.haar s :=
  LeftCosetSpace.discreteQuotientMeasure_eq (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G) Measure.haar hs

/-- Any actual norm-one fundamental domain gives the same norm-one quotient measure. -/
theorem normOneRationalQuotientHaarMeasure_eq {s : Set (normOneSubgroup F G)}
    (hs : IsFundamentalDomain (rationalNormOneSubgroup F G) s Measure.haar) :
    normOneRationalQuotientHaarMeasure F G =
      LeftCosetSpace.quotientMeasure (rationalNormOneSubgroup F G) Measure.haar s :=
  LeftCosetSpace.discreteQuotientMeasure_eq (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G) Measure.haar hs

/-- The actual full rational quotient satisfies the real counting-measure Weil formula. -/
theorem integral_rationalQuotientAverageReal (f : C_c(AdelicGroupPoints F G, ℝ)) :
    (∫ q, Langlands.QuotientIntegration.quotientAverageReal
      (rationalSubgroup F G) Measure.count f q ∂rationalQuotientHaarMeasure F G) =
        ∫ x, f x ∂Measure.haar :=
  LeftCosetSpace.integral_quotientAverageReal_count (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G) Measure.haar f

/-- The same real Weil formula on the actual norm-one rational quotient. -/
theorem integral_normOneRationalQuotientAverageReal (f : C_c(normOneSubgroup F G, ℝ)) :
    (∫ q, Langlands.QuotientIntegration.quotientAverageReal
      (rationalNormOneSubgroup F G) Measure.count f q
        ∂normOneRationalQuotientHaarMeasure F G) = ∫ x, f x ∂Measure.haar :=
  LeftCosetSpace.integral_quotientAverageReal_count (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G) Measure.haar f

/-- Positive right translation preserves the full quotient when ambient Haar is right invariant. -/
theorem measurePreserving_rightTranslate_rationalQuotientHaarMeasure
    [(Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant]
    (g : AdelicGroupPoints F G) :
    MeasurePreserving (LeftCosetSpace.rightTranslate (rationalSubgroup F G) g)
      (rationalQuotientHaarMeasure F G) (rationalQuotientHaarMeasure F G) :=
  LeftCosetSpace.measurePreserving_rightTranslate_haarQuotientMeasure
    (rationalSubgroup F G) (isDiscrete_rationalSubgroup F G) g

/-- Positive right translation preserves the norm-one quotient under the analogous hypothesis. -/
theorem measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (g : normOneSubgroup F G) :
    MeasurePreserving (LeftCosetSpace.rightTranslate (rationalNormOneSubgroup F G) g)
      (normOneRationalQuotientHaarMeasure F G) (normOneRationalQuotientHaarMeasure F G) :=
  LeftCosetSpace.measurePreserving_rightTranslate_haarQuotientMeasure
    (rationalNormOneSubgroup F G) (isDiscrete_rationalNormOneSubgroup F G) g

/-- Full complex Weil compatibility, retaining the analytic right-invariance obligation. -/
theorem rationalQuotientHaarMeasure_isCompatible
    [(Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant] :
    Langlands.QuotientIntegration.IsCompatible (rationalSubgroup F G)
      Measure.haar Measure.count (rationalQuotientHaarMeasure F G) :=
  LeftCosetSpace.haarQuotientMeasure_isCompatible (rationalSubgroup F G)
    (isDiscrete_rationalSubgroup F G)

/-- Norm-one complex Weil compatibility, with the actual ambient Haar normalization. -/
theorem normOneRationalQuotientHaarMeasure_isCompatible
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] :
    Langlands.QuotientIntegration.IsCompatible (rationalNormOneSubgroup F G)
      Measure.haar Measure.count (normOneRationalQuotientHaarMeasure F G) :=
  LeftCosetSpace.haarQuotientMeasure_isCompatible (rationalNormOneSubgroup F G)
    (isDiscrete_rationalNormOneSubgroup F G)

/-- Bundle the exact norm-one quotient measure with its complex Weil compatibility. -/
def compatibleNormOneRationalQuotientHaarMeasure
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] :
    Subtype (fun (quotientMeasure : Measure (NormOneRationalQuotient F G)) =>
      Langlands.QuotientIntegration.IsCompatible (rationalNormOneSubgroup F G)
        Measure.haar Measure.count quotientMeasure) :=
  ⟨normOneRationalQuotientHaarMeasure F G,
    normOneRationalQuotientHaarMeasure_isCompatible F G⟩

@[simp] theorem compatibleNormOneRationalQuotientHaarMeasure_val
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] :
    (compatibleNormOneRationalQuotientHaarMeasure F G).val =
      normOneRationalQuotientHaarMeasure F G := rfl

end Langlands.Global.AdelicGroupPoints
