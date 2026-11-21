import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement
import Langlands.Automorphic.CuspidalTranslatedHilbertEmbedding
import Langlands.Automorphic.OperatorDeterminantSliceHaar
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters

/-! # The determinant band and the positive-central quotient of `GL_n`

The determinant band `1 < |det| < 2` of the principal quotient `[GL_n]` projects onto the
positive-central quotient `Q`, and the band measure pushes forward to a positive finite
multiple of the quotient Haar measure of `Q`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Automorphic.RealizationSummand

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance bandMeasureIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance bandMeasureSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-! ### The determinant norm is an algebraic character norm -/

/-- The determinant character evaluated on adelic points is the matrix determinant. -/
theorem character_determinant (x : AdelicGroupPoints F GLG) :
    character F GLG (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of F)).toMul x =
      Matrix.GeneralLinearGroup.det (GeneralLinearGroupPoints.adelicHomeomorph F n x) := by
  let S := CommAlgCat.of (CommRingCat.of F) (AdeleRing (𝓞 F) F)
  have h := GeneralLinear.characterOnAffineMatrices_determinantCharacter S
    (GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F) S x)
  change Gm.affineUnitsEquiv (CommRingCat.of F) S
    (((GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F) S).symm
      (GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F) S x)) ≫
        (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of F)).toMul.hom.hom) = _ at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

/-- The determinant norm of the band is the character norm of the determinant. -/
theorem groupDeterminantNorm_eq_characterNorm (x : AdelicGroupPoints F GLG) :
    OperatorDeterminantSlice.groupDeterminantNorm F n x =
      characterNorm F GLG
        (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of F)).toMul x := by
  change IdeleAbsoluteValue.full F
      (AdelicGL.determinant F n (GeneralLinearGroupPoints.adelicHomeomorph F n x)) =
    IdeleAbsoluteValue.full F (character F GLG
      (GeneralLinear.determinantCharacter (Fin n) (CommRingCat.of F)).toMul x)
  rw [character_determinant]
  rfl

/-- Norm-one adelic points have determinant norm one. -/
theorem groupDeterminantNorm_normOne (m : normOneSubgroup F GLG) :
    OperatorDeterminantSlice.groupDeterminantNorm F n m = 1 := by
  rw [groupDeterminantNorm_eq_characterNorm]
  exact (mem_normOneSubgroup F GLG _).mp m.property _


/-! ### The projection onto the positive-central quotient -/

variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))

/-- The projection from the principal rational quotient onto the positive-central rational
quotient. -/
def projection : OperatorDeterminantSlice.Quotient F n → PositiveRationalQuotient F GLG T i :=
  LeftCosetSpace.lift (rationalSubgroup F GLG)
    (LeftCosetSpace.mk (positiveRationalSubgroup F GLG T i)) (fun g x =>
      LeftCosetSpace.mk_subgroup_mul (positiveRationalSubgroup F GLG T i)
        ⟨g, rationalSubgroup_le_positiveRationalSubgroup F GLG T i g.property⟩ x)

@[simp] theorem projection_mk (x : AdelicGroupPoints F GLG) :
    projection F n T i (LeftCosetSpace.mk (rationalSubgroup F GLG) x) =
      LeftCosetSpace.mk (positiveRationalSubgroup F GLG T i) x := rfl

theorem projection_surjective : Function.Surjective (projection F n T i) := fun q => by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (positiveRationalSubgroup F GLG T i) q
  exact ⟨LeftCosetSpace.mk (rationalSubgroup F GLG) x, rfl⟩

theorem continuous_projection : Continuous (projection F n T i) :=
  LeftCosetSpace.continuous_lift _ _ _ (LeftCosetSpace.continuous_mk _)

theorem measurable_projection : Measurable (projection F n T i) :=
  measurable_from_quotient.mpr (LeftCosetSpace.measurable_mk _)

theorem projection_rightTranslate (g : AdelicGroupPoints F GLG)
    (q : OperatorDeterminantSlice.Quotient F n) :
    projection F n T i (LeftCosetSpace.rightTranslate (rationalSubgroup F GLG) g q) =
      LeftCosetSpace.rightTranslate (positiveRationalSubgroup F GLG T i) g
        (projection F n T i q) := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F GLG) q
  rfl

theorem measurable_normOneToPositiveQuotient :
    Measurable (normOneToPositiveQuotient F GLG T i) :=
  measurable_from_quotient.mpr ((LeftCosetSpace.measurable_mk _).comp measurable_subtype_coe)

/-! ### A fundamental domain adapted to the positive/norm-one decomposition -/

variable (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

/-- The chosen Borel fundamental domain of the norm-one principal quotient. -/
def normOneDomain : Set (normOneSubgroup F GLG) :=
  LeftCosetSpace.fundamentalDomain (rationalNormOneSubgroup F GLG)
    (isDiscrete_rationalNormOneSubgroup F GLG)

/-- Its pullback along the norm-one factor of the positive/norm-one decomposition. -/
def adaptedDomain : Set (AdelicGroupPoints F GLG) :=
  normOneFactor F GLG T i hi I e ⁻¹' normOneDomain F n

theorem measurableSet_normOneDomain : MeasurableSet (normOneDomain F n) :=
  LeftCosetSpace.measurableSet_fundamentalDomain _ _

theorem measurableSet_adaptedDomain : MeasurableSet (adaptedDomain F n T i hi I e) :=
  (measurableSet_normOneDomain F n).preimage
    (continuous_normOneFactor F GLG T i hi I e).measurable

theorem normOneProjection_rational_val (g : rationalSubgroup F GLG) :
    (normOneProjection F GLG T i hi I e hc (g : AdelicGroupPoints F GLG) :
      AdelicGroupPoints F GLG) = g :=
  congrArg Subtype.val (normOneProjection_normOne F GLG T i hi I e hc
    ⟨g, rationalSubgroup_le_normOneSubgroup F GLG g.property⟩)

theorem normOneProjection_rational_mem (g : rationalSubgroup F GLG) :
    normOneProjection F GLG T i hi I e hc (g : AdelicGroupPoints F GLG) ∈
      rationalNormOneSubgroup F GLG := by
  obtain ⟨q, hq⟩ := g.property
  rw [← hq, normOneProjection_rational]
  exact ⟨q, rfl⟩

include hc in
/-- The pulled-back domain is a fundamental domain for the principal rational subgroup. -/
theorem isFundamentalDomain_adaptedDomain :
    IsFundamentalDomain (rationalSubgroup F GLG) (adaptedDomain F n T i hi I e) Measure.haar := by
  refine IsFundamentalDomain.mk' (measurableSet_adaptedDomain F n T i hi I e).nullMeasurableSet ?_
  intro x
  let P := normOneProjection F GLG T i hi I e hc
  obtain ⟨g₁, hg₁, huniq⟩ := LeftCosetSpace.fundamentalDomain_unique
    (rationalNormOneSubgroup F GLG) (isDiscrete_rationalNormOneSubgroup F GLG) (P x)
  have hP (g : rationalSubgroup F GLG) :
      normOneFactor F GLG T i hi I e ((g : AdelicGroupPoints F GLG) * x) =
        P (g : AdelicGroupPoints F GLG) * P x :=
    map_mul P _ _
  refine ⟨rationalNormOneSubgroupInclusion F GLG g₁, ?_, ?_⟩
  · change normOneFactor F GLG T i hi I e
      (((rationalNormOneSubgroupInclusion F GLG g₁ : rationalSubgroup F GLG) :
        AdelicGroupPoints F GLG) * x) ∈ normOneDomain F n
    rw [hP]
    have h1 : P ((rationalNormOneSubgroupInclusion F GLG g₁ : rationalSubgroup F GLG) :
        AdelicGroupPoints F GLG) = (g₁ : normOneSubgroup F GLG) :=
      normOneProjection_normOne F GLG T i hi I e hc (g₁ : normOneSubgroup F GLG)
    rw [h1]
    exact hg₁
  · intro d hd
    change normOneFactor F GLG T i hi I e ((d : AdelicGroupPoints F GLG) * x) ∈
      normOneDomain F n at hd
    rw [hP] at hd
    have hd₁ := huniq ⟨P (d : AdelicGroupPoints F GLG),
      normOneProjection_rational_mem F n T i hi I e hc d⟩ hd
    apply Subtype.ext
    rw [← normOneProjection_rational_val F n T i hi I e hc d]
    exact congrArg (fun z : rationalNormOneSubgroup F GLG =>
      ((z : normOneSubgroup F GLG) : AdelicGroupPoints F GLG)) hd₁


/-! ### The band measure pushes forward to a multiple of the quotient measure -/

/-- Positive points whose determinant norm lies in the band `(1, 2)`. -/
def positiveBand : Set (intrinsicSubgroup F T) :=
  {a | 1 < (OperatorDeterminantSlice.groupDeterminantNorm F n
      (positivePointMap F GLG T i a) : ℝ≥0) ∧
    (OperatorDeterminantSlice.groupDeterminantNorm F n
      (positivePointMap F GLG T i a) : ℝ≥0) < 2}

/-- The comparison constant: normalized positive Haar measure of the positive band. -/
def bandConstant : ℝ≥0∞ :=
  normalizedPositiveHaarMeasure F GLG T i hi I e hc (positiveBand F n T i)

theorem preimage_band_inter_adaptedDomain (A : Set (PositiveRationalQuotient F GLG T i)) :
    normOneDecomposition F GLG T i hi I e ⁻¹'
        (LeftCosetSpace.mk (rationalSubgroup F GLG) ⁻¹'
          (projection F n T i ⁻¹' A ∩ OperatorDeterminantSlice.band F n) ∩
            adaptedDomain F n T i hi I e) =
      positiveBand F n T i ×ˢ (LeftCosetSpace.mk (rationalNormOneSubgroup F GLG) ⁻¹'
        (normOneToPositiveQuotient F GLG T i ⁻¹' A) ∩ normOneDomain F n) := by
  ext ⟨a, m⟩
  have hD : normOneFactor F GLG T i hi I e (positivePointMap F GLG T i a * m) = m :=
    congrArg Prod.snd ((normOneDecomposition F GLG T i hi I e).symm_apply_apply (a, m))
  have hQ : LeftCosetSpace.mk (positiveRationalSubgroup F GLG T i)
      (positivePointMap F GLG T i a * m) =
        LeftCosetSpace.mk (positiveRationalSubgroup F GLG T i) (m : AdelicGroupPoints F GLG) :=
    LeftCosetSpace.mk_subgroup_mul _ ⟨_, imageSubgroup_le_positiveRationalSubgroup F GLG T i
      ⟨a.val, a.property, rfl⟩⟩ _
  have hN : OperatorDeterminantSlice.groupDeterminantNorm F n
      (positivePointMap F GLG T i a * m) =
        OperatorDeterminantSlice.groupDeterminantNorm F n (positivePointMap F GLG T i a) := by
    rw [map_mul, groupDeterminantNorm_normOne, mul_one]
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, normOneDecomposition_apply,
    projection_mk, adaptedDomain, hD, hQ, OperatorDeterminantSlice.band, Set.mem_ofPred_eq,
    OperatorDeterminantSlice.quotientDeterminantNorm_mk, hN, positiveBand,
    normOneToPositiveQuotient_mk]
  tauto

include hc in
/-- **Band comparison.** The pushforward of the band-restricted principal quotient measure
to the positive-central quotient is `bandConstant` times its quotient Haar measure. -/
theorem map_bandMeasure :
    Measure.map (projection F n T i)
        ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
          (OperatorDeterminantSlice.band F n)) =
      bandConstant F n T i hi I e hc • positiveRationalQuotientHaarMeasure F GLG T i := by
  ext A hA
  have hpA : MeasurableSet (projection F n T i ⁻¹' A) := measurable_projection F n T i hA
  have hset : MeasurableSet (projection F n T i ⁻¹' A ∩ OperatorDeterminantSlice.band F n) :=
    hpA.inter (OperatorDeterminantSlice.measurableSet_band F n)
  have hπA : MeasurableSet (normOneToPositiveQuotient F GLG T i ⁻¹' A) :=
    measurable_normOneToPositiveQuotient F n T i hA
  rw [Measure.map_apply (measurable_projection F n T i) hA,
    Measure.restrict_apply hpA, Measure.smul_apply, smul_eq_mul,
    positiveRationalQuotientHaarMeasure_apply F GLG T i hi I e hc]
  rw [show OperatorDeterminantSlice.quotientHaarMeasure F n =
      LeftCosetSpace.quotientMeasure (rationalSubgroup F GLG) Measure.haar
        (adaptedDomain F n T i hi I e) from
    rationalQuotientHaarMeasure_eq F GLG (isFundamentalDomain_adaptedDomain F n T i hi I e hc)]
  rw [LeftCosetSpace.quotientMeasure_apply _ _ _ hset,
    ← map_normalizedPositiveHaarMeasure_prod F GLG T i hi I e hc,
    Measure.map_apply (normOneDecomposition F GLG T i hi I e).continuous.measurable
      (((LeftCosetSpace.measurable_mk _) hset).inter (measurableSet_adaptedDomain F n T i hi I e)),
    preimage_band_inter_adaptedDomain, Measure.prod_prod]
  change _ = _ * LeftCosetSpace.quotientMeasure (rationalNormOneSubgroup F GLG) Measure.haar
    (normOneDomain F n) _
  rw [LeftCosetSpace.quotientMeasure_apply _ _ _ hπA]
  rfl


/-! ### Consequences of the band comparison -/

include hc in
/-- In positive rank the band has positive measure, so the comparison constant is nonzero. -/
theorem bandConstant_ne_zero (hn : n ≠ 0) : bandConstant F n T i hi I e hc ≠ 0 := by
  intro h0
  have hmap := map_bandMeasure F n T i hi I e hc
  rw [h0, zero_smul] at hmap
  obtain ⟨z, hz⟩ := OperatorDeterminantSlice.exists_scalar_determinantNorm F n hn
    (Units.mk0 (3 / 2 : ℝ≥0) (by norm_num))
  have hmem : OperatorDeterminantSlice.point F n (AdelicGL.scalar F n z) ∈
      OperatorDeterminantSlice.band F n := by
    simp only [OperatorDeterminantSlice.band, Set.mem_ofPred_eq,
      OperatorDeterminantSlice.quotientDeterminantNorm_point, hz, Units.val_mk0]
    constructor <;> norm_num
  have hpos : 0 < OperatorDeterminantSlice.quotientHaarMeasure F n
      (OperatorDeterminantSlice.band F n) :=
    (OperatorDeterminantSlice.isOpen_band F n).measure_pos _ ⟨_, hmem⟩
  have huniv := congrArg (fun m : Measure (PositiveRationalQuotient F GLG T i) => m Set.univ) hmap
  simp only [Measure.map_apply (measurable_projection F n T i) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.coe_zero, Pi.zero_apply] at huniv
  exact hpos.ne' huniv

include hc in
/-- Band integrals of pulled-back functions are `bandConstant` times quotient integrals. -/
theorem lintegral_band (g : PositiveRationalQuotient F GLG T i → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q, g (projection F n T i q) ∂((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
        (OperatorDeterminantSlice.band F n)) =
      bandConstant F n T i hi I e hc * ∫⁻ x, g x ∂positiveRationalQuotientHaarMeasure F GLG T i := by
  rw [← lintegral_map hg (measurable_projection F n T i), map_bandMeasure F n T i hi I e hc,
    lintegral_smul_measure, smul_eq_mul]

include hc in
/-- Band integrals of pulled-back functions are `bandConstant` times quotient integrals. -/
theorem integral_band (g : PositiveRationalQuotient F GLG T i → ℂ)
    (hg : AEStronglyMeasurable g (positiveRationalQuotientHaarMeasure F GLG T i)) :
    ∫ q, g (projection F n T i q) ∂((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
        (OperatorDeterminantSlice.band F n)) =
      (bandConstant F n T i hi I e hc).toReal • ∫ x, g x ∂positiveRationalQuotientHaarMeasure F GLG T i := by
  rw [← integral_map (measurable_projection F n T i).aemeasurable
      (by rw [map_bandMeasure F n T i hi I e hc]; exact hg.smul_measure _),
    map_bandMeasure F n T i hi I e hc, integral_smul_measure]

include hc in
theorem eLpNorm_comp_projection (g : PositiveRationalQuotient F GLG T i → ℂ)
    (hg : AEStronglyMeasurable g (positiveRationalQuotientHaarMeasure F GLG T i)) :
    eLpNorm (g ∘ projection F n T i) 2
        ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
          (OperatorDeterminantSlice.band F n)) =
      bandConstant F n T i hi I e hc ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm g 2 (positiveRationalQuotientHaarMeasure F GLG T i) := by
  rw [← eLpNorm_map_measure
      (by rw [map_bandMeasure F n T i hi I e hc]; exact hg.smul_measure _)
      (measurable_projection F n T i).aemeasurable,
    map_bandMeasure F n T i hi I e hc,
    eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ hg, smul_eq_mul]

include hi e hc in
/-- Square integrability of a pullback on the band gives square integrability on the quotient. -/
theorem memLp_of_comp_projection (hn : n ≠ 0) (g : PositiveRationalQuotient F GLG T i → ℂ)
    (hg : AEStronglyMeasurable g (positiveRationalQuotientHaarMeasure F GLG T i))
    (hL2 : MemLp (g ∘ projection F n T i) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
        (OperatorDeterminantSlice.band F n))) :
    MemLp g 2 (positiveRationalQuotientHaarMeasure F GLG T i) := by
  rw [memLp_iff]
  have h := hL2.eLpNorm_lt_top
  rw [eLpNorm_comp_projection F n T i hi I e hc g hg] at h
  refine ENNReal.lt_top_of_mul_ne_top_right h.ne ?_
  rw [Ne, ENNReal.rpow_eq_zero_iff]
  have := bandConstant_ne_zero F n T i hi I e hc hn
  norm_num [this]

include hc in
/-- Square-integrable quotient functions pull back to square-integrable band functions when
the comparison constant is finite. -/
theorem memLp_comp_projection (hc' : bandConstant F n T i hi I e hc ≠ ⊤)
    (g : PositiveRationalQuotient F GLG T i → ℂ)
    (hL2 : MemLp g 2 (positiveRationalQuotientHaarMeasure F GLG T i)) :
    MemLp (g ∘ projection F n T i) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
        (OperatorDeterminantSlice.band F n)) := by
  rw [memLp_iff, eLpNorm_comp_projection F n T i hi I e hc g hL2.aestronglyMeasurable]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hc') hL2.eLpNorm_lt_top

include hc in
/-- A nonzero continuous quotient function whose pullback is square integrable on the band
forces the comparison constant to be finite. -/
theorem bandConstant_ne_top
    [(Measure.haar : Measure (normOneSubgroup F GLG)).IsMulRightInvariant]
    (h : C(PositiveRationalQuotient F GLG T i, ℂ)) (hne : h ≠ 0)
    (hL2 : MemLp (h ∘ projection F n T i) 2
      ((OperatorDeterminantSlice.quotientHaarMeasure F n).restrict
        (OperatorDeterminantSlice.band F n))) :
    bandConstant F n T i hi I e hc ≠ ⊤ := by
  let _ := positiveRationalQuotient_borelSpace F GLG T i hi I e hc
  have := GroupSchemeFunctions.haarQuotientMeasure_isOpenPosMeasure F GLG T i hi I e hc
  intro htop
  have hm := hL2.eLpNorm_lt_top
  rw [eLpNorm_comp_projection F n T i hi I e hc h h.continuous.aestronglyMeasurable, htop,
    ENNReal.top_rpow_of_pos (by norm_num)] at hm
  have hpos : eLpNorm h 2 (positiveRationalQuotientHaarMeasure F GLG T i) ≠ 0 := by
    rw [Ne, eLpNorm_eq_zero_iff two_ne_zero]
    intro hae
    apply hne
    ext x
    exact congrFun ((h.continuous.ae_eq_iff_eq _ continuous_const).mp hae) x
  rw [ENNReal.top_mul hpos] at hm
  exact lt_irrefl _ hm

end Langlands.Automorphic.RealizationSummand
