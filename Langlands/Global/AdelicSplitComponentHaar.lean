import Langlands.Global.AdelicSplitComponentIndependence
import Langlands.Global.AdelicSplitCenterHaarIndependence

/-! # Exact normalized Haar comparison between actual split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable (I : Type u) [Fintype I]
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
variable (T' : CommGroupScheme (Spec (CommRingCat.of F))) (i' : T'.toGrp ⟶ G)
variable (hi' : Function.Injective (characterRestrict i'))
variable [(characterRestrict i').range.FiniteIndex]
variable (J : Type u) [Fintype J]
variable (e' : T'.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) J)

/-- Compare actual positive groups through their common ambient character-log dual. -/
def positiveComparisonEquiv : intrinsicSubgroup F T ≃ₜ* intrinsicSubgroup F T' :=
  (positiveAmbientLogEquiv F G T i hi I e).trans
    (positiveAmbientLogEquiv F G T' i' hi' J e').symm

@[simp] theorem positiveComparisonEquiv_apply (a : intrinsicSubgroup F T) :
    positiveComparisonEquiv F G T i hi I e T' i' hi' J e' a =
      positiveFactor F G T' i' hi' J e' (positivePointMap F G T i a) := by
  rw [positiveFactor_apply, characterLogHom_positivePointMap F G T i hi I e]
  rfl

/-- Equality of the actual positive images makes the comparison preserve ambient points. -/
theorem positivePointMap_positiveComparisonEquiv
    (himage : imageSubgroup F T G i = imageSubgroup F T' G i')
    (a : intrinsicSubgroup F T) :
    positivePointMap F G T' i'
      (positiveComparisonEquiv F G T i hi I e T' i' hi' J e' a) =
        positivePointMap F G T i a := by
  have ha : positivePointMap F G T i a ∈ imageSubgroup F T' G i' := by
    rw [← himage]
    exact ⟨a.val, a.property, rfl⟩
  obtain ⟨b, hb, he⟩ := ha
  have he' : positivePointMap F G T' i' ⟨b, hb⟩ = positivePointMap F G T i a := he
  rw [positiveComparisonEquiv_apply, ← he', positiveFactor_positivePointMap]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The same positive image gives exact transport of the fixed normalized positive Haar. -/
theorem measurePreserving_positiveComparisonEquiv
    (hc : IsCentral i) (hc' : IsCentral i')
    (himage : imageSubgroup F T G i = imageSubgroup F T' G i') :
    MeasurePreserving (positiveComparisonEquiv F G T i hi I e T' i' hi' J e')
      (normalizedPositiveHaarMeasure F G T i hi I e hc)
      (normalizedPositiveHaarMeasure F G T' i' hi' J e' hc') := by
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  have hm : Measurable (positiveComparisonEquiv F G T i hi I e T' i' hi' J e') :=
    (positiveComparisonEquiv F G T i hi I e T' i' hi' J e').continuous.measurable
  have hd : Measurable (normOneDecomposition F G T' i' hi' J e') :=
    (normOneDecomposition F G T' i' hi' J e').continuous.measurable
  refine ⟨hm, ?_⟩
  apply normalizedPositiveHaarMeasure_unique F G T' i' hi' J e' hc'
  have hprod :=
    Measure.map_prod_map (normalizedPositiveHaarMeasure F G T i hi I e hc)
      (Measure.haar : Measure (normOneSubgroup F G)) hm measurable_id
  simp only [Measure.map_id] at hprod
  rw [hprod, Measure.map_map hd (hm.prodMap measurable_id)]
  have hcomp : (normOneDecomposition F G T' i' hi' J e') ∘
      Prod.map (positiveComparisonEquiv F G T i hi I e T' i' hi' J e') id =
        normOneDecomposition F G T i hi I e := by
    funext p
    change positivePointMap F G T' i'
      (positiveComparisonEquiv F G T i hi I e T' i' hi' J e' p.1) * p.2 =
        positivePointMap F G T i p.1 * p.2
    rw [positivePointMap_positiveComparisonEquiv F G T i hi I e T' i' hi' J e' himage]
  rw [hcomp]
  exact map_normalizedPositiveHaarMeasure_prod F G T i hi I e hc

/-- Equality of the full actual subgroups gives the identity on ambient representatives. -/
def splitComponentSubgroupEquiv (hs : IsSplitComponent i) (hs' : IsSplitComponent i') :
    positiveRationalSubgroup F G T i ≃ₜ* positiveRationalSubgroup F G T' i' where
  toMulEquiv := MulEquiv.subgroupCongr
    (positiveRationalSubgroup_eq_of_splitComponents F G hs hs')
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

omit [(characterRestrict i).range.FiniteIndex] [(characterRestrict i').range.FiniteIndex] in
@[simp] theorem splitComponentSubgroupEquiv_val
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i')
    (x : positiveRationalSubgroup F G T i) :
    (splitComponentSubgroupEquiv F G T i T' i' hs hs' x : AdelicGroupPoints F G) = x :=
  rfl

/-- The positive and principal multiplication charts commute with split-component change. -/
theorem splitComponentSubgroupEquiv_positiveRationalDecomposition
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i')
    (p : intrinsicSubgroup F T × rationalNormOneSubgroup F G) :
    splitComponentSubgroupEquiv F G T i T' i' hs hs'
      (positiveRationalDecomposition F G T i hi I e hs.1.2 p) =
        positiveRationalDecomposition F G T' i' hi' J e' hs'.1.2
          (positiveComparisonEquiv F G T i hi I e T' i' hi' J e' p.1, p.2) := by
  apply Subtype.ext
  change positivePointMap F G T i p.1 * p.2.val.val =
    positivePointMap F G T' i'
      (positiveComparisonEquiv F G T i hi I e T' i' hi' J e' p.1) * p.2.val.val
  rw [positivePointMap_positiveComparisonEquiv F G T i hi I e T' i' hi' J e'
    (imageSubgroup_eq_of_splitComponents F G hs hs')]

/-- The identity on the actual full subgroups preserves the exact Haar normalization. -/
theorem measurePreserving_splitComponentSubgroupEquiv
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i') :
    MeasurePreserving (splitComponentSubgroupEquiv F G T i T' i' hs hs')
      (positiveRationalSubgroupHaarMeasure F G T i hi I e hs.1.2)
      (positiveRationalSubgroupHaarMeasure F G T' i' hi' J e' hs'.1.2) := by
  let := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hs.1.2
  have hm : Measurable (splitComponentSubgroupEquiv F G T i T' i' hs hs') :=
    (splitComponentSubgroupEquiv F G T i T' i' hs hs').continuous.measurable
  have hd : Measurable (positiveRationalDecomposition F G T i hi I e hs.1.2) :=
    (positiveRationalDecomposition F G T i hi I e hs.1.2).continuous.measurable
  have hd' : Measurable (positiveRationalDecomposition F G T' i' hi' J e' hs'.1.2) :=
    (positiveRationalDecomposition F G T' i' hi' J e' hs'.1.2).continuous.measurable
  have hprod :=
    (measurePreserving_positiveComparisonEquiv F G T i hi I e T' i' hi' J e'
      hs.1.2 hs'.1.2 (imageSubgroup_eq_of_splitComponents F G hs hs')).prod
        (MeasurePreserving.id (Measure.count : Measure (rationalNormOneSubgroup F G)))
  have hcomp : (splitComponentSubgroupEquiv F G T i T' i' hs hs') ∘
      positiveRationalDecomposition F G T i hi I e hs.1.2 =
        (positiveRationalDecomposition F G T' i' hi' J e' hs'.1.2) ∘
          Prod.map (positiveComparisonEquiv F G T i hi I e T' i' hi' J e') id := by
    funext p
    exact splitComponentSubgroupEquiv_positiveRationalDecomposition
      F G T i hi I e T' i' hi' J e' hs hs' p
  refine ⟨hm, ?_⟩
  unfold positiveRationalSubgroupHaarMeasure
  rw [Measure.map_map hm hd, hcomp, ← Measure.map_map hd' hprod.measurable, hprod.map_eq]

/-- The positive comparison also preserves the measures constructed without coordinates. -/
theorem measurePreserving_positiveComparisonEquiv_intrinsic
    (hc : IsCentral i) (hc' : IsCentral i')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (himage : imageSubgroup F T G i = imageSubgroup F T' G i') :
    MeasurePreserving (positiveComparisonEquiv F G T i hi I e T' i' hi' J e')
      (intrinsicPositiveHaarMeasure F G T i hi hc hT)
      (intrinsicPositiveHaarMeasure F G T' i' hi' hc' hT') := by
  rw [intrinsicPositiveHaarMeasure_eq F G T i hi I e hc hT,
    intrinsicPositiveHaarMeasure_eq F G T' i' hi' J e' hc' hT']
  exact measurePreserving_positiveComparisonEquiv
    F G T i hi I e T' i' hi' J e' hc hc' himage

/-- Full intrinsic subgroup Haar is independent of the supplied actual split component. -/
theorem measurePreserving_splitComponentSubgroupEquiv_intrinsic
    (hs : IsSplitComponent i) (hs' : IsSplitComponent i') :
    MeasurePreserving (splitComponentSubgroupEquiv F G T i T' i' hs hs')
      (intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hs.1.2 hs.1.1.1)
      (intrinsicPositiveRationalSubgroupHaarMeasure F G T' i' hi' hs'.1.2 hs'.1.1.1) := by
  obtain ⟨K, hK, ⟨d⟩⟩ := hs.1.1.1
  obtain ⟨L, hL, ⟨d'⟩⟩ := hs'.1.1.1
  let := hK
  let := hL
  let := Fintype.ofFinite K
  let := Fintype.ofFinite L
  rw [intrinsicPositiveRationalSubgroupHaarMeasure_eq F G T i hi K d hs.1.2 hs.1.1.1,
    intrinsicPositiveRationalSubgroupHaarMeasure_eq F G T' i' hi' L d' hs'.1.2 hs'.1.1.1]
  exact measurePreserving_splitComponentSubgroupEquiv
    F G T i hi K d T' i' hi' L d' hs hs'

end Langlands.Global.PositiveRealTorus
