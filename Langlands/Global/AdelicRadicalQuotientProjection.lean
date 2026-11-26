import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicPositiveImageClosed
import Langlands.Global.EisensteinConstantTerm.Points

/-! # Probability measures under projections of compact radical quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G M U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine M.X.left] [IsAffine U.X.left] [IsAffine V.X.left]
  (j : U ⟶ G) (k : V ⟶ M) [IsClosedImmersion j.hom.hom.left] [IsClosedImmersion k.hom.hom.left]

/-- A closed subgroup representative gives a topological group equivalence
onto the adelic points of its range functor. -/
def adelicRangeEquiv : AdelicGroupPoints F U ≃ₜ* adelicPoints F G (SubgroupFunctor.range j) := by
  let hj := AdelicGroupPoints.isClosedEmbedding_map F U G j
  let e := MulEquiv.ofBijective (adelicRangeMap F j)
    (⟨fun x y h => hj.injective (congrArg Subtype.val h), adelicRangeMap_surjective F j⟩)
  refine ⟨e, continuous_adelicRangeMap F j, ?_⟩
  apply hj.isEmbedding.isInducing.continuous_iff.mpr
  have he : (AdelicGroupPoints.map F U G j) ∘ e.symm = Subtype.val := by
    funext x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  change Continuous ((AdelicGroupPoints.map F U G j) ∘ e.symm)
  rw [he]
  exact continuous_subtype_val

@[simp]
theorem adelicRangeEquiv_apply (x : AdelicGroupPoints F U) :
    adelicRangeEquiv j x = adelicRangeMap F j x := rfl

variable (π : U ⟶ V)

local notation "A" => adelicPoints F G (SubgroupFunctor.range j)
local notation "B" => adelicPoints F M (SubgroupFunctor.range k)
local notation "ΓA" => rationalSubgroup F G (SubgroupFunctor.range j)
local notation "ΓB" => rationalSubgroup F M (SubgroupFunctor.range k)
local notation "QA" => RationalQuotient F G (SubgroupFunctor.range j)
local notation "QB" => RationalQuotient F M (SubgroupFunctor.range k)
local notation "μA" => normalizedRationalQuotientHaarMeasure F G (SubgroupFunctor.range j)
local notation "μB" => normalizedRationalQuotientHaarMeasure F M (SubgroupFunctor.range k)

local instance : IsClosed (A : Set (AdelicGroupPoints F G)) := isClosed_adelicPoints_range F G j
local instance closedRangeTarget : IsClosed (B : Set (AdelicGroupPoints F M)) := isClosed_adelicPoints_range F M k

/-- A map on represented subgroup points, expressed in their ambient ranges. -/
def adelicRangeProjection : A →ₜ* B :=
  (ContinuousMonoidHom.toContinuousMonoidHom (adelicRangeEquiv k)).comp
    ((AdelicGroupPoints.map F U V π).comp (ContinuousMonoidHom.toContinuousMonoidHom (adelicRangeEquiv j).symm))

@[simp]
theorem adelicRangeProjection_apply (x : AdelicGroupPoints F U) :
    adelicRangeProjection j k π (adelicRangeMap F j x) =
      adelicRangeMap F k (AdelicGroupPoints.map F U V π x) := by
  change adelicRangeEquiv k (AdelicGroupPoints.map F U V π
    ((adelicRangeEquiv j).symm (adelicRangeEquiv j x))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, adelicRangeEquiv_apply]

private theorem adelicRangeProjection_mem_rational {x : A} (hx : x ∈ ΓA) :
    adelicRangeProjection j k π x ∈ ΓB := by
  obtain ⟨q, hq⟩ := (AdelicGroupPoints.mem_rationalSubgroup_range_iff j x).mp hx
  have hx' : adelicRangeMap F j (AdelicGroupPoints.rational F U q) = x := Subtype.ext hq
  rw [← hx', adelicRangeProjection_apply, AdelicGroupPoints.map_rational π]
  exact (AdelicGroupPoints.mem_rationalSubgroup_range_iff k _).mpr ⟨_, rfl⟩

/-- The projection on left quotients induced by the map of actual point groups. -/
def radicalQuotientProjection : QA → QB :=
  LeftCosetSpace.lift ΓA (fun x : A => LeftCosetSpace.mk ΓB (adelicRangeProjection j k π x))
    (fun r x => by
      rw [map_mul]
      exact LeftCosetSpace.mk_subgroup_mul ΓB
        ⟨_, adelicRangeProjection_mem_rational j k π r.property⟩ _)

@[simp]
theorem radicalQuotientProjection_mk (x : A) :
    radicalQuotientProjection j k π (LeftCosetSpace.mk ΓA x) =
      LeftCosetSpace.mk ΓB (adelicRangeProjection j k π x) := rfl

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]

local instance : BorelSpace QA := rationalQuotientBorelSpace F G (SubgroupFunctor.range j)
local instance : BorelSpace QB := rationalQuotientBorelSpace F M (SubgroupFunctor.range k)

/-- A surjection on adelic points pushes the normalized quotient probability
forward to the normalized quotient probability of the target range. -/
theorem measurePreserving_radicalQuotientProjection [CompactSpace QA] [CompactSpace QB]
    (hπ : Function.Surjective (AdelicGroupPoints.map F U V π)) :
    MeasurePreserving (radicalQuotientProjection j k π) μA μB := by
  let e := radicalQuotientProjection j k π
  let ν := Measure.map e μA
  have he : Continuous e := (LeftCosetSpace.continuous_iff ΓA).mpr
    ((LeftCosetSpace.continuous_mk ΓB).comp (adelicRangeProjection j k π).continuous)
  have hm : Measurable e := he.measurable
  have hΓ := isDiscrete_rationalSubgroup F M (SubgroupFunctor.range k)
  let : IsClosed (ΓB : Set B) := (ΓB).isClosed_of_isDiscrete hΓ
  let : DiscreteTopology ΓB := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let : LocallyCompactSpace B := (closedRangeTarget k).locallyCompactSpace
  let := LeftCosetSpace.isFiniteMeasureOnCompacts_count ΓB hΓ
  let : (Measure.count : Measure ΓB).IsHaarMeasure :=
    { toIsOpenPosMeasure := ⟨fun _ _ hs => Measure.count_ne_zero hs⟩ }
  let : IsProbabilityMeasure μA := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G _
  let : IsProbabilityMeasure μB := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F M _
  let : IsProbabilityMeasure ν := ⟨by simp [ν, Measure.map_apply hm MeasurableSet.univ]⟩
  let : (μB).Regular := (compactCompatibleNormalizedRationalQuotientMeasure F M
    (SubgroupFunctor.range k)).property.2.regular
  let : (μA).Regular := (compactCompatibleNormalizedRationalQuotientMeasure F G
    (SubgroupFunctor.range j)).property.2.regular
  let : ν.InnerRegularCompactLTTop := Measure.InnerRegularCompactLTTop.map_of_continuous he
  let : ν.Regular := inferInstance
  have hsurj : Function.Surjective (adelicRangeProjection j k π) :=
    (adelicRangeEquiv k).surjective.comp (hπ.comp (adelicRangeEquiv j).symm.surjective)
  have hright (y : B) : MeasurePreserving (LeftCosetSpace.rightTranslate ΓB y) ν ν := by
    obtain ⟨x, rfl⟩ := hsurj y
    have hx := measurePreserving_rightTranslate_of_compactRationalQuotient F G (SubgroupFunctor.range j) x
    have hy := measurePreserving_rightTranslate_of_compactRationalQuotient F M (SubgroupFunctor.range k)
      (adelicRangeProjection j k π x)
    have hcomm : LeftCosetSpace.rightTranslate ΓB (adelicRangeProjection j k π x) ∘ e =
        e ∘ LeftCosetSpace.rightTranslate ΓA x := by
      funext q
      obtain ⟨v, rfl⟩ := LeftCosetSpace.mk_surjective ΓA q
      change LeftCosetSpace.mk ΓB
        (adelicRangeProjection j k π v * adelicRangeProjection j k π x) =
          LeftCosetSpace.mk ΓB (adelicRangeProjection j k π (v * x))
      rw [map_mul]
    refine ⟨hy.measurable, ?_⟩
    change Measure.map (LeftCosetSpace.rightTranslate ΓB _) (Measure.map e μA) = ν
    rw [Measure.map_map hy.measurable hm, hcomm, ← Measure.map_map hm hx.measurable, hx.map_eq]
  exact ⟨hm, LeftCosetSpace.eq_of_rightInvariant_probability ΓB
    ((ΓB).isClosed_of_isDiscrete hΓ) Measure.count ν μB hright
    (measurePreserving_rightTranslate_of_compactRationalQuotient F M (SubgroupFunctor.range k))⟩

end Langlands.Global.AdelicSubgroupPoints
