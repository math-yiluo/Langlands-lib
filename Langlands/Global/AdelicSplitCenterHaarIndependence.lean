import Langlands.Global.AdelicSplitCenterSubgroupHaar

/-! # Independence of split-torus coordinates in normalized adelic Haar measures -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (i : T.toGrp ⟶ G)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The fixed ambient and norm-one Haar measures uniquely determine the positive measure. -/
theorem normalizedPositiveHaarMeasure_unique (hc : IsCentral i)
    (positiveMeasure : Measure (intrinsicSubgroup F T))
    (hpositive : Measure.map (normOneDecomposition F G T i hi I e)
      (positiveMeasure.prod (Measure.haar : Measure (normOneSubgroup F G))) =
        (Measure.haar : Measure (AdelicGroupPoints F G))) :
    positiveMeasure = normalizedPositiveHaarMeasure F G T i hi I e hc := by
  have hp : positiveMeasure.prod (Measure.haar : Measure (normOneSubgroup F G)) =
      (normalizedPositiveHaarMeasure F G T i hi I e hc).prod
        (Measure.haar : Measure (normOneSubgroup F G)) :=
    (normOneDecomposition F G T i hi I e).toMeasurableEquiv.measurableEmbedding.map_injective
      (hpositive.trans (map_normalizedPositiveHaarMeasure_prod F G T i hi I e hc).symm)
  obtain ⟨s, hs, hso, hsf⟩ :=
    (Measure.haar : Measure (normOneSubgroup F G)).exists_isOpen_measure_lt_top 1
  have hsp : 0 < (Measure.haar : Measure (normOneSubgroup F G)) s :=
    hso.measure_pos _ ⟨1, hs⟩
  ext a ha
  have h := congrArg
    (fun m : Measure (intrinsicSubgroup F T × normOneSubgroup F G) => m (a ×ˢ s)) hp
  rw [Measure.prod_prod, Measure.prod_prod] at h
  exact (ENNReal.mul_left_inj hsp.ne' hsf.ne).mp h

variable (J : Type u) [Fintype J]
variable (e' : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J)

/-- Changing the finite splitting coordinates leaves the normalized positive measure equal. -/
theorem normalizedPositiveHaarMeasure_eq_of_splitting (hc : IsCentral i) :
    normalizedPositiveHaarMeasure F G T i hi I e hc =
      normalizedPositiveHaarMeasure F G T i hi J e' hc := by
  symm
  apply normalizedPositiveHaarMeasure_unique F G T i hi I e hc
  exact map_normalizedPositiveHaarMeasure_prod F G T i hi J e' hc

/-- The full positive-times-principal subgroup Haar measure has the same independence. -/
theorem positiveRationalSubgroupHaarMeasure_eq_of_splitting (hc : IsCentral i) :
    positiveRationalSubgroupHaarMeasure F G T i hi I e hc =
      positiveRationalSubgroupHaarMeasure F G T i hi J e' hc := by
  unfold positiveRationalSubgroupHaarMeasure
  rw [normalizedPositiveHaarMeasure_eq_of_splitting F G T i hi I e J e' hc]
  rfl

/-- Normalized positive Haar from the split-torus property, without supplied coordinates. -/
def intrinsicPositiveHaarMeasure (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    Measure (intrinsicSubgroup F T) := by
  letI : Finite hT.choose := hT.choose_spec.1
  letI := Fintype.ofFinite hT.choose
  exact normalizedPositiveHaarMeasure F G T i hi hT.choose
    (Classical.choice hT.choose_spec.2) hc

/-- The intrinsic construction agrees with the normalization for every supplied splitting. -/
theorem intrinsicPositiveHaarMeasure_eq (hc : IsCentral i) (hT : IsSplitTorus T.toGrp) :
    intrinsicPositiveHaarMeasure F G T i hi hc hT =
      normalizedPositiveHaarMeasure F G T i hi I e hc := by
  let : Finite hT.choose := hT.choose_spec.1
  let := Fintype.ofFinite hT.choose
  unfold intrinsicPositiveHaarMeasure
  exact normalizedPositiveHaarMeasure_eq_of_splitting F G T i hi _ _ I e hc

theorem intrinsicPositiveHaarMeasure_isHaarMeasure (hc : IsCentral i)
    (hT : IsSplitTorus T.toGrp) :
    (intrinsicPositiveHaarMeasure F G T i hi hc hT).IsHaarMeasure := by
  let : Finite hT.choose := hT.choose_spec.1
  let := Fintype.ofFinite hT.choose
  unfold intrinsicPositiveHaarMeasure
  exact normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi _ _ hc

/-- Every actual multiplication chart preserves the intrinsic positive normalization. -/
theorem measurePreserving_normOneDecomposition_intrinsic (hc : IsCentral i)
    (hT : IsSplitTorus T.toGrp) :
    MeasurePreserving (normOneDecomposition F G T i hi I e)
      ((intrinsicPositiveHaarMeasure F G T i hi hc hT).prod
        (Measure.haar : Measure (normOneSubgroup F G)))
      (Measure.haar : Measure (AdelicGroupPoints F G)) := by
  rw [intrinsicPositiveHaarMeasure_eq F G T i hi I e hc hT]
  exact measurePreserving_normOneDecomposition F G T i hi I e hc

/-- Full subgroup Haar from the split-torus property, without supplied coordinates. -/
def intrinsicPositiveRationalSubgroupHaarMeasure (hc : IsCentral i)
    (hT : IsSplitTorus T.toGrp) : Measure (positiveRationalSubgroup F G T i) := by
  letI : Finite hT.choose := hT.choose_spec.1
  letI := Fintype.ofFinite hT.choose
  exact positiveRationalSubgroupHaarMeasure F G T i hi hT.choose
    (Classical.choice hT.choose_spec.2) hc

theorem intrinsicPositiveRationalSubgroupHaarMeasure_eq (hc : IsCentral i)
    (hT : IsSplitTorus T.toGrp) :
    intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT =
      positiveRationalSubgroupHaarMeasure F G T i hi I e hc := by
  let : Finite hT.choose := hT.choose_spec.1
  let := Fintype.ofFinite hT.choose
  unfold intrinsicPositiveRationalSubgroupHaarMeasure
  exact positiveRationalSubgroupHaarMeasure_eq_of_splitting F G T i hi _ _ I e hc

theorem intrinsicPositiveRationalSubgroupHaarMeasure_isHaarMeasure (hc : IsCentral i)
    (hT : IsSplitTorus T.toGrp) :
    (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT).IsHaarMeasure := by
  let : Finite hT.choose := hT.choose_spec.1
  let := Fintype.ofFinite hT.choose
  unfold intrinsicPositiveRationalSubgroupHaarMeasure
  exact positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi _ _ hc

end Langlands.Global.PositiveRealTorus
