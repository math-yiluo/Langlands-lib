import Langlands.Global.ArthurTruncationRadicalInvariance
import Langlands.Global.AdelicConstantTermComposition
import Langlands.Global.CompactQuotientSubgroupAverageIntegrable

/-! # Nested averaging for measurable Arthur cutoff kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  AdelicGroupPoints ArthurParabolicSpaces EisensteinConstantTerm ConstantTermComposition

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

section Radicals

variable {U V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left] [IsAffine V.X.left]
  (jU : U ⟶ G) (jV : V ⟶ G) [IsClosedImmersion jU.hom.hom.left]
  [IsClosedImmersion jV.hom.hom.left]

local notation "A" => SubgroupFunctor.range jU
local notation "B" => SubgroupFunctor.range jV

/-- Nested normalized constant terms collapse to the average over the larger radical. -/
theorem subgroupConstantTerm_subgroupConstantTerm_of_le
    (hle : A ≤ B) (hn : SubgroupFunctor.IsNormalizedBy A B)
    (hUs : Smooth U.X.hom) (hUc : ConnectedSpace U.X.left) (hUu : IsUnipotent U)
    (hVs : Smooth V.X.hom) (hVc : ConnectedSpace V.X.left) (hVu : IsUnipotent V)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ)
    (g : AdelicGroupPoints F G) :
    subgroupConstantTerm F jV (subgroupConstantTerm F jU φ) g =
      subgroupConstantTerm F jV φ g := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G A : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G jU
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G B : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G jV
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G A) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F jU hUs hUc hUu
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G B) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F jV hVs hVc hVu
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G B
  let Δ := AdelicSubgroupPoints.rationalSubgroup F G A
  let j := AdelicSubgroupPoints.adelicInclusion F G hle
  let mU := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G A
  let mV := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G B
  let : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G A) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G A
  let : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G B) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G B
  have hΓ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G B
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let : (Measure.count : Measure Γ).IsHaarMeasure := rationalSubgroup_count_isHaarMeasure' F G
  let : IsProbabilityMeasure mU := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G A
  let : IsProbabilityMeasure mV := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G B
  let : mV.Regular :=
    (AdelicSubgroupPoints.compactCompatibleNormalizedRationalQuotientMeasure F G B).property.2.regular
  let s := LeftCosetSpace.fundamentalDomain Γ hΓ
  let ρ := (AdelicSubgroupPoints.normalizedHaarMeasure F G B).restrict s
  have hpush : Measure.map (LeftCosetSpace.mk Γ) ρ = mV :=
    (normalizedRationalQuotientHaarMeasure_eq_quotientMeasure B).symm
  let : IsFiniteMeasure ρ := (Measure.isFiniteMeasure_map_iff (LeftCosetSpace.measurable_mk Γ).aemeasurable).mp
    (hpush.symm ▸ (inferInstance : IsFiniteMeasure mV))
  have hj : Δ ≤ Γ.comap j := AdelicSubgroupPoints.rationalSubgroup_le_comap_adelicInclusion F G hle
  have hjc : Continuous j := continuous_subtype_val.subtype_mk _
  have hconj := LeftCosetSpace.subgroupAverageConjugation Γ Δ j hj mU (by
    rintro ⟨_, q, rfl⟩
    let a := AdelicSubgroupPoints.adelicNormalizerConj F G hn (AdelicSubgroupPoints.rational F G B q⁻¹)
    have ha := AdelicSubgroupPoints.adelicNormalizerConj_mem_rationalSubgroup_iff F G hn q⁻¹
    refine ⟨a, ha, AdelicSubgroupPoints.measurePreserving_rationalQuotientAutomorphism F G A a ha,
      fun n => ?_⟩
    apply Subtype.ext
    change (a n : AdelicGroupPoints F G) =
      (AdelicSubgroupPoints.rational F G B q : AdelicGroupPoints F G)⁻¹ * n *
        (AdelicSubgroupPoints.rational F G B q : AdelicGroupPoints F G)
    simp [a])
  have hinv : ConstantTermComposition.IsRationalInvariant F G B φ := fun r hr y =>
    hφ.2.2 _ (rationalImage_le_rationalSubgroup jV ((mem_rationalSubgroup_range_iff jV r).mp hr)) y
  let f := descendedIntegrand hinv g
  have hfm : Measurable f := by
    apply measurable_from_quotient.mpr
    exact hφ.1.comp (continuous_subtype_val.mul_const g).measurable
  have hfi : Integrable f mV := by
    obtain ⟨Ω, hΩ, hrep⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F jV hVs hVc hVu
    obtain ⟨M, hM⟩ := hφ.2.1 ((Subtype.val '' Ω) * {g}) ((hΩ.image continuous_subtype_val).mul isCompact_singleton)
    apply (integrable_const (max M 0)).mono hfm.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun q => ?_
    obtain ⟨r, hr, hq⟩ := hrep q.out
    rw [show f q = φ (((q.out : AdelicSubgroupPoints.adelicPoints F G B) : AdelicGroupPoints F G) * g)
      from descendedIntegrand_out hinv g q, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have he := hinv r hr ((q.out : AdelicSubgroupPoints.adelicPoints F G B).val * g)
    rw [← he, ← mul_assoc]
    exact (hM _ ⟨_, ⟨r * q.out, hq, rfl⟩, g, rfl, rfl⟩).trans (le_max_left _ _)
  have havg := LeftCosetSpace.integral_compactSubgroupAverage_of_integrable Γ Δ j hj hjc mU hconj
    (Γ.isClosed_of_isDiscrete hΓ) Measure.count mV
    (AdelicSubgroupPoints.measurePreserving_rightTranslate_of_compactRationalQuotient F G B)
    ρ hpush hfm.stronglyMeasurable hfi
  refine Eq.trans ?_ (havg.trans ?_)
  · apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x => ?_
    have hx : LeftCosetSpace.mk Γ x.out = x := Quotient.out_eq x
    rw [← hx, LeftCosetSpace.compactSubgroupAverage_mk, hx]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun y => ?_
    have hy : LeftCosetSpace.mk Δ y.out = y := Quotient.out_eq y
    conv_rhs => rw [← hy]
    exact congrArg φ (mul_assoc _ _ _).symm
  · exact integral_congr_ae (Filter.Eventually.of_forall (descendedIntegrand_out hinv g))

end Radicals

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

include hν in
/-- Applying a smaller parabolic's constant term to a cutoff kernel replaces the
constant term in the kernel by the smaller parabolic's and preserves the cutoff. -/
theorem constantTerm_cutoffKernel_of_subset {S J : Set (characterLattice T)}
    (hSJ : S ⊆ J) (hJ : J ⊆ simpleRelativeRoots i ν) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ)
    (g : AdelicGroupPoints F G) :
    constantTerm F i ν S (cutoffKernel hG hi D hK hρ J Tp φ) g =
      constantTerm F i ν S φ g * (ArthurRelative.tauHat hG hi ν D J
        (simpleRelativeRoots i ν) (height hi hK hρ g - Tp) : ℂ) := by
  have hS := hSJ.trans hJ
  have hU := (Standard.parabolicStructure i ν hG hi hν J hJ).2.2.1.1
  have hV := (Standard.parabolicStructure i ν hG hi hν S hS).2.2.1.1
  have havg := subgroupConstantTerm_subgroupConstantTerm_of_le
    (Standard.unipotentHom i ν J) (Standard.unipotentHom i ν S)
    (unipotentRange_le hG hi hν hSJ hJ) (unipotentRange_isNormalizedBy hG hi hν hSJ hJ)
    hU.smooth hU.connectedSpace hU.isUnipotent hV.smooth hV.connectedSpace hV.isUnipotent φ hφ g
  let R := SubgroupFunctor.range (Standard.unipotentHom i ν S)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G R : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (Standard.unipotentHom i ν S)
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G R
  let c := (ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν) (height hi hK hρ g - Tp) : ℂ)
  unfold constantTerm
  change (∫ q : AdelicSubgroupPoints.RationalQuotient F G R,
    cutoffKernel hG hi D hK hρ J Tp φ
      (((q.out : AdelicSubgroupPoints.adelicPoints F G R) : AdelicGroupPoints F G) * g) ∂m) = _
  calc
    _ = ∫ q : AdelicSubgroupPoints.RationalQuotient F G R, constantTerm F i ν J φ
          (((q.out : AdelicSubgroupPoints.adelicPoints F G R) : AdelicGroupPoints F G) * g) * c ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        unfold cutoffKernel
        dsimp only
        rw [height_radical_mul hG hi hν hK hρ hS
          (q.out : AdelicSubgroupPoints.adelicPoints F G R) g]
    _ = constantTerm F i ν S φ g * c := by rw [integral_mul_const]; exact congrArg (· * c) havg

end Langlands.Global.ArthurTruncation.Idempotence
