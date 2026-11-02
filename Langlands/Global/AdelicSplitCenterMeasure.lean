import Langlands.Global.AdelicSplitCenterQuotient
import Langlands.Global.AdelicGroupHaarMeasure

/-! # Exact norm-one measure on the actual positive-central rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Topology CompactlySupported

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)
variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Push the exact existing norm-one quotient Haar measure through actual inclusion.
The comparison hypotheses below establish its measure-theoretic properties. -/
def positiveRationalQuotientHaarMeasure : Measure (PositiveRationalQuotient F G T i) :=
  Measure.map (normOneToPositiveQuotient F G T i) (normOneRationalQuotientHaarMeasure F G)

variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

include hi I e in
/-- The inherited quotient sigma algebra is Borel for the actual quotient topology. -/
theorem positiveRationalQuotient_borelSpace (hc : IsCentral i) :
    BorelSpace (PositiveRationalQuotient F G T i) := by
  let := positiveRationalQuotient_t2Space F G T i hi I e hc
  exact LeftCosetSpace.quotient_borelSpace (positiveRationalSubgroup F G T i)

/-- The actual quotient homeomorphism is measurable in both inherited sigma algebras. -/
def positiveQuotientMeasurableEquiv (hc : IsCentral i) :
    NormOneRationalQuotient F G ≃ᵐ PositiveRationalQuotient F G T i := by
  letI := positiveRationalQuotient_borelSpace F G T i hi I e hc
  exact (positiveQuotientHomeomorph F G T i hi I e hc).toMeasurableEquiv

@[simp] theorem positiveQuotientMeasurableEquiv_apply (hc : IsCentral i)
    (q : NormOneRationalQuotient F G) :
    positiveQuotientMeasurableEquiv F G T i hi I e hc q =
      normOneToPositiveQuotient F G T i q := rfl

@[simp] theorem positiveQuotientMeasurableEquiv_symm_apply (hc : IsCentral i)
    (q : PositiveRationalQuotient F G T i) :
    (positiveQuotientMeasurableEquiv F G T i hi I e hc).symm q =
      positiveQuotientToNormOne F G T i hi I e hc q := rfl

/-- The actual comparison preserves the exact norm-one quotient normalization. -/
theorem measurePreserving_positiveQuotient (hc : IsCentral i) :
    MeasurePreserving (positiveQuotientMeasurableEquiv F G T i hi I e hc)
      (normOneRationalQuotientHaarMeasure F G)
      (positiveRationalQuotientHaarMeasure F G T i) :=
  ⟨(positiveQuotientMeasurableEquiv F G T i hi I e hc).measurable, rfl⟩

theorem measurePreserving_positiveQuotient_symm (hc : IsCentral i) :
    MeasurePreserving (positiveQuotientMeasurableEquiv F G T i hi I e hc).symm
      (positiveRationalQuotientHaarMeasure F G T i)
      (normOneRationalQuotientHaarMeasure F G) :=
  MeasurePreserving.symm _ (measurePreserving_positiveQuotient F G T i hi I e hc)

/-- The inverse pushforward is the existing norm-one measure, with no scalar factor. -/
theorem map_positiveQuotient_symm (hc : IsCentral i) :
    Measure.map (positiveQuotientToNormOne F G T i hi I e hc)
      (positiveRationalQuotientHaarMeasure F G T i) =
        normOneRationalQuotientHaarMeasure F G :=
  (measurePreserving_positiveQuotient_symm F G T i hi I e hc).map_eq

/-- Exact inverse normalization characterizes the transported measure uniquely. -/
theorem eq_positiveRationalQuotientHaarMeasure_iff (hc : IsCentral i)
    (ν : Measure (PositiveRationalQuotient F G T i)) :
    ν = positiveRationalQuotientHaarMeasure F G T i ↔
      Measure.map (positiveQuotientToNormOne F G T i hi I e hc) ν =
        normOneRationalQuotientHaarMeasure F G := by
  constructor
  · rintro rfl
    exact map_positiveQuotient_symm F G T i hi I e hc
  · intro hν
    apply MeasurableEquiv.map_measurableEquiv_injective
      (positiveQuotientMeasurableEquiv F G T i hi I e hc).symm
    exact hν.trans (map_positiveQuotient_symm F G T i hi I e hc).symm

include hi I e in
theorem positiveRationalQuotientHaarMeasure_ne_zero (hc : IsCentral i) :
    positiveRationalQuotientHaarMeasure F G T i ≠ 0 :=
  (Measure.map_ne_zero_iff
    (positiveQuotientMeasurableEquiv F G T i hi I e hc).measurable.aemeasurable).2
      (normOneRationalQuotientHaarMeasure_ne_zero F G)

include hi I e in
theorem positiveRationalQuotientHaarMeasure_regular (hc : IsCentral i) :
    (positiveRationalQuotientHaarMeasure F G T i).Regular := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  exact Measure.Regular.map (positiveQuotientHomeomorph F G T i hi I e hc)

include hi I e in
theorem positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure (hc : IsCentral i) :
    IsLocallyFiniteMeasure (positiveRationalQuotientHaarMeasure F G T i) := by
  let := positiveRationalQuotientHaarMeasure_regular F G T i hi I e hc
  infer_instance

include hi I e in
/-- This set formula holds for every set, with no measurable-set restriction. -/
theorem positiveRationalQuotientHaarMeasure_apply (hc : IsCentral i)
    (s : Set (PositiveRationalQuotient F G T i)) :
    positiveRationalQuotientHaarMeasure F G T i s =
      normOneRationalQuotientHaarMeasure F G (normOneToPositiveQuotient F G T i ⁻¹' s) :=
  (positiveQuotientMeasurableEquiv F G T i hi I e hc).map_apply s

include hi I e in
theorem positiveRationalQuotientHaarMeasure_univ (hc : IsCentral i) :
    positiveRationalQuotientHaarMeasure F G T i univ =
      normOneRationalQuotientHaarMeasure F G univ := by
  rw [positiveRationalQuotientHaarMeasure_apply F G T i hi I e hc]
  rfl

include hi I e in
/-- Finiteness is transported exactly; no finite-volume assertion is assumed or proved here. -/
theorem positiveRationalQuotientHaarMeasure_isFiniteMeasure_iff (hc : IsCentral i) :
    IsFiniteMeasure (positiveRationalQuotientHaarMeasure F G T i) ↔
      IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) := by
  rw [isFiniteMeasure_iff, isFiniteMeasure_iff,
    positiveRationalQuotientHaarMeasure_univ F G T i hi I e hc]

include hi I e in
/-- Convergence of a complex function is equivalent to convergence after actual inclusion. -/
theorem integrable_positiveRationalQuotientHaarMeasure_iff (hc : IsCentral i)
    (f : PositiveRationalQuotient F G T i → ℂ) :
    Integrable f (positiveRationalQuotientHaarMeasure F G T i) ↔
      Integrable (fun q => f (normOneToPositiveQuotient F G T i q))
        (normOneRationalQuotientHaarMeasure F G) :=
  integrable_map_equiv (positiveQuotientMeasurableEquiv F G T i hi I e hc) f

include hi I e in
/-- Equality of total Bochner integrals; convergence is the separate preceding theorem. -/
theorem integral_positiveRationalQuotientHaarMeasure (hc : IsCentral i)
    (f : PositiveRationalQuotient F G T i → ℂ) :
    (∫ q, f q ∂positiveRationalQuotientHaarMeasure F G T i) =
      ∫ q, f (normOneToPositiveQuotient F G T i q)
        ∂normOneRationalQuotientHaarMeasure F G :=
  integral_map_equiv (positiveQuotientMeasurableEquiv F G T i hi I e hc) f

omit [LocallyOfFiniteType G.X.hom] in
/-- Transfer the actual norm-one counting average to the positive rational quotient.
This is not orbital integration over the full positive/principal subgroup. -/
def positiveNormOneQuotientAverage (hc : IsCentral i) (f : normOneSubgroup F G → ℂ) :
    PositiveRationalQuotient F G T i → ℂ :=
  fun q => Langlands.QuotientIntegration.quotientAverage
    (rationalNormOneSubgroup F G) Measure.count f
      (positiveQuotientToNormOne F G T i hi I e hc q)

omit [LocallyOfFiniteType G.X.hom] in
@[simp] theorem positiveNormOneQuotientAverage_mk (hc : IsCentral i)
    (f : normOneSubgroup F G → ℂ) (x : AdelicGroupPoints F G) :
    positiveNormOneQuotientAverage F G T i hi I e hc f
      (LeftCosetSpace.mk (positiveRationalSubgroup F G T i) x) =
        ∫ q : rationalNormOneSubgroup F G,
          f (q.val * normOneProjection F G T i hi I e hc x) ∂Measure.count := rfl

omit [LocallyOfFiniteType G.X.hom] in
@[simp] theorem positiveNormOneQuotientAverage_normOneToPositiveQuotient (hc : IsCentral i)
    (f : normOneSubgroup F G → ℂ) (q : NormOneRationalQuotient F G) :
    positiveNormOneQuotientAverage F G T i hi I e hc f
      (normOneToPositiveQuotient F G T i q) =
        Langlands.QuotientIntegration.quotientAverage
          (rationalNormOneSubgroup F G) Measure.count f q :=
  congrArg (Langlands.QuotientIntegration.quotientAverage
    (rationalNormOneSubgroup F G) Measure.count f)
      ((positiveQuotientHomeomorph F G T i hi I e hc).left_inv q)

section RightInvariant

variable [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

include hi I e in
/-- Every ambient positive right translation preserves the transported quotient measure. -/
theorem measurePreserving_rightTranslate_positiveRationalQuotientHaarMeasure
    (hc : IsCentral i) (g : AdelicGroupPoints F G) :
    MeasurePreserving (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) g)
      (positiveRationalQuotientHaarMeasure F G T i)
      (positiveRationalQuotientHaarMeasure F G T i) :=
  (measurePreserving_positiveQuotient F G T i hi I e hc).of_semiconj
    (measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure F G
      (normOneProjection F G T i hi I e hc g))
    (positiveQuotientHomeomorph_rightTranslate F G T i hi I e hc g)
    (LeftCosetSpace.measurable_rightTranslate (positiveRationalSubgroup F G T i) g)

/-- The transferred average is integrable for every continuous compactly supported input. -/
theorem integrable_positiveNormOneQuotientAverage (hc : IsCentral i)
    (f : normOneSubgroup F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (positiveNormOneQuotientAverage F G T i hi I e hc f)
      (positiveRationalQuotientHaarMeasure F G T i) := by
  apply (integrable_positiveRationalQuotientHaarMeasure_iff F G T i hi I e hc _).2
  simp only [positiveNormOneQuotientAverage_normOneToPositiveQuotient]
  exact (normOneRationalQuotientHaarMeasure_isCompatible F G).averaging_integrable f hf hfc

/-- The exact norm-one Weil formula after transport to the positive rational quotient. -/
theorem integral_positiveNormOneQuotientAverage (hc : IsCentral i)
    (f : normOneSubgroup F G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ q, positiveNormOneQuotientAverage F G T i hi I e hc f q
      ∂positiveRationalQuotientHaarMeasure F G T i) = ∫ x, f x ∂Measure.haar := by
  rw [integral_positiveRationalQuotientHaarMeasure F G T i hi I e hc]
  simp only [positiveNormOneQuotientAverage_normOneToPositiveQuotient]
  exact (normOneRationalQuotientHaarMeasure_isCompatible F G).integral_formula f hf hfc

end RightInvariant

end Langlands.Global.PositiveRealTorus
