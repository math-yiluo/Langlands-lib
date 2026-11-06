import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.Analysis.Local.QuotientInvariantComparison
import Langlands.Analysis.Local.QuotientMeasureEquiv

/-! # Actual subgroup rational quotients under group-scheme isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Opposite Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} (e : G ≅ H)
  (V : SubgroupFunctor H)

/-- The actual coefficient-point group isomorphism restricted to a subgroup functor
and its inverse image, without a representability assumption. -/
def coefficientSubgroupIso (A : CommAlgCat.{u} (CommRingCat.of F)) :
    ((V.comap e.hom).carrier ((algSpec (CommRingCat.of F)).obj (op A))) ≃*
      V.carrier ((algSpec (CommRingCat.of F)).obj (op A)) := by
  let a := ((yonedaGrp.mapIso e).app (op ((algSpec (CommRingCat.of F)).obj (op A)))).groupIsoToMulEquiv
  exact
    { toFun := fun x => ⟨a x.val, x.property⟩
      invFun := fun y => ⟨a.symm y.val, by
        change a (a.symm y.val) ∈ V.carrier _
        simpa only [a.apply_symm_apply] using y.property⟩
      left_inv := fun x => Subtype.ext (a.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (a.apply_symm_apply y.val)
      map_mul' := fun x y => Subtype.ext (a.map_mul x.val y.val) }

omit [NumberField F] in
@[simp]
theorem coefficientSubgroupIso_coe (A : CommAlgCat.{u} (CommRingCat.of F))
    (x : (V.comap e.hom).carrier ((algSpec (CommRingCat.of F)).obj (op A))) :
    (coefficientSubgroupIso F e V A x : H.affinePoints A) =
      G.affinePointsTarget e.hom A x := rfl

variable [IsAffine G.X.left] [IsAffine H.X.left]

/-- The restricted isomorphism on actual full adelic subgroups, with their inherited topologies. -/
def adelicSubgroupIso :
    adelicPoints F G (V.comap e.hom) ≃ₜ* adelicPoints F H V where
  toMulEquiv := coefficientSubgroupIso F e V (CommAlgCat.of F (AdeleRing (𝓞 F) F))
  continuous_toFun :=
    ((G.continuous_affinePointsTarget (CommAlgCat.of F (AdeleRing (𝓞 F) F)) e.hom).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((H.continuous_affinePointsTarget (CommAlgCat.of F (AdeleRing (𝓞 F) F)) e.inv).comp
      continuous_subtype_val).subtype_mk _

omit [IsAffine G.X.left] [IsAffine H.X.left] in
/-- The isomorphism respects the actual principal maps, rather than only their ambient images. -/
theorem adelicSubgroupIso_rational (q : rationalPoints F G (V.comap e.hom)) :
    adelicSubgroupIso F e V (rational F G (V.comap e.hom) q) =
      rational F H V (coefficientSubgroupIso F e V (CommAlgCat.of F F) q) := by
  apply Subtype.ext
  exact (congrArg (fun f => f q.val) (AdelicGroupPoints.rational_naturality F G e.hom)).symm

omit [IsAffine G.X.left] [IsAffine H.X.left] in
/-- The two principal subgroups correspond exactly under the actual adelic isomorphism. -/
theorem adelicSubgroupIso_mem_rationalSubgroup_iff
    (x : adelicPoints F G (V.comap e.hom)) :
    adelicSubgroupIso F e V x ∈ rationalSubgroup F H V ↔
      x ∈ rationalSubgroup F G (V.comap e.hom) := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨(coefficientSubgroupIso F e V (CommAlgCat.of F F)).symm q, ?_⟩
    apply (adelicSubgroupIso F e V).injective
    rw [adelicSubgroupIso_rational, MulEquiv.apply_symm_apply]
    exact hq
  · rintro ⟨q, rfl⟩
    exact ⟨coefficientSubgroupIso F e V (CommAlgCat.of F F) q,
      (adelicSubgroupIso_rational F e V q).symm⟩

/-- The induced homeomorphism of the actual rational left quotients. -/
def rationalQuotientIso :
    RationalQuotient F G (V.comap e.hom) ≃ₜ RationalQuotient F H V :=
  Homeomorph.Quotient.congr (adelicSubgroupIso F e V).toHomeomorph (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ rationalSubgroup F G (V.comap e.hom) ↔
      adelicSubgroupIso F e V y * (adelicSubgroupIso F e V x)⁻¹ ∈ rationalSubgroup F H V
    rw [← map_inv, ← map_mul]
    exact (adelicSubgroupIso_mem_rationalSubgroup_iff F e V (y * x⁻¹)).symm)

omit [IsAffine G.X.left] [IsAffine H.X.left] in
@[simp]
theorem rationalQuotientIso_mk (x : adelicPoints F G (V.comap e.hom)) :
    rationalQuotientIso F e V (LeftCosetSpace.mk (rationalSubgroup F G (V.comap e.hom)) x) =
      LeftCosetSpace.mk (rationalSubgroup F H V) (adelicSubgroupIso F e V x) := rfl

omit [IsAffine G.X.left] [IsAffine H.X.left] in
/-- The induced map intertwines positive right translation by the corresponding actual subgroup point. -/
theorem rationalQuotientIso_rightTranslate (x : adelicPoints F G (V.comap e.hom))
    (q : RationalQuotient F G (V.comap e.hom)) :
    rationalQuotientIso F e V
        (LeftCosetSpace.rightTranslate (rationalSubgroup F G (V.comap e.hom)) x q) =
      LeftCosetSpace.rightTranslate (rationalSubgroup F H V) (adelicSubgroupIso F e V x)
        (rationalQuotientIso F e V q) := by
  induction q using Quotient.inductionOn with
  | _ y =>
    exact congrArg (LeftCosetSpace.mk (rationalSubgroup F H V))
      ((adelicSubgroupIso F e V).map_mul y x)

omit [IsAffine G.X.left] [IsAffine H.X.left] in
/-- Closedness pulls back on the original full adelic point groups. -/
theorem isClosed_adelicPoints_comap
    [hV : IsClosed (adelicPoints F H V : Set (AdelicGroupPoints F H))] :
    IsClosed (adelicPoints F G (V.comap e.hom) : Set (AdelicGroupPoints F G)) :=
  hV.preimage
    (G.continuous_affinePointsTarget (CommAlgCat.of F (AdeleRing (𝓞 F) F)) e.hom)

omit [IsAffine G.X.left] [IsAffine H.X.left] in
/-- Compactness of the actual rational quotient transports through the constructed map. -/
theorem rationalQuotientCompactSpace_comap [CompactSpace (RationalQuotient F H V)] :
    CompactSpace (RationalQuotient F G (V.comap e.hom)) :=
  (rationalQuotientIso F e V).symm.compactSpace

section CompactMeasure

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  [hV : IsClosed (adelicPoints F H V : Set (AdelicGroupPoints F H))]
  [CompactSpace (RationalQuotient F H V)]

local instance transportSourceClosed :
    IsClosed (adelicPoints F G (V.comap e.hom) : Set (AdelicGroupPoints F G)) :=
  isClosed_adelicPoints_comap F e V

local instance transportSourceCompact : CompactSpace (RationalQuotient F G (V.comap e.hom)) :=
  rationalQuotientCompactSpace_comap F e V

local instance transportSourceLocallyCompact : LocallyCompactSpace
    (adelicPoints F G (V.comap e.hom)) :=
  (isClosed_adelicPoints_comap F e V).locallyCompactSpace

local instance transportTargetLocallyCompact : LocallyCompactSpace (adelicPoints F H V) :=
  hV.locallyCompactSpace

local instance transportSourcePolish : PolishSpace (adelicPoints F G (V.comap e.hom)) :=
  (isClosed_adelicPoints_comap F e V).polishSpace

local instance transportTargetPolish : PolishSpace (adelicPoints F H V) :=
  hV.polishSpace

local instance transportSourceBorel : BorelSpace (RationalQuotient F G (V.comap e.hom)) :=
  rationalQuotientBorelSpace F G (V.comap e.hom)

local instance transportTargetBorel : BorelSpace (RationalQuotient F H V) :=
  rationalQuotientBorelSpace F H V

/-- Actual group-scheme isomorphisms preserve the intrinsic compact-quotient probability,
including its normalization, with no supplied Haar modulus. -/
theorem measurePreserving_rationalQuotientIso :
    MeasurePreserving (rationalQuotientIso F e V)
      (normalizedRationalQuotientHaarMeasure F G (V.comap e.hom))
      (normalizedRationalQuotientHaarMeasure F H V) := by
  let ν₁ := normalizedRationalQuotientHaarMeasure F G (V.comap e.hom)
  let ν₂ := normalizedRationalQuotientHaarMeasure F H V
  let E := rationalQuotientIso F e V
  let a := adelicSubgroupIso F e V
  let Γ := rationalSubgroup F H V
  have hΓ : IsDiscrete (Γ : Set (adelicPoints F H V)) := isDiscrete_rationalSubgroup F H V
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let : (Measure.count : Measure Γ).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := LeftCosetSpace.isFiniteMeasureOnCompacts_count Γ hΓ
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := ⟨fun _ _ hne => Measure.count_ne_zero hne⟩ }
  let : IsProbabilityMeasure ν₁ :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G (V.comap e.hom)
  let : IsProbabilityMeasure ν₂ :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F H V
  have hreg₁ : ν₁.Regular :=
    (compactCompatibleNormalizedRationalQuotientMeasure F G (V.comap e.hom)).property.2.regular
  have hreg₂ : ν₂.Regular :=
    (compactCompatibleNormalizedRationalQuotientMeasure F H V).property.2.regular
  have hreg : (Measure.map E ν₁).Regular := Measure.Regular.map E
  let : IsProbabilityMeasure (Measure.map E ν₁) := inferInstance
  have hinv : ∀ g : adelicPoints F H V,
      MeasurePreserving (Langlands.QuotientIntegration.rightTranslate Γ g)
        (Measure.map E ν₁) (Measure.map E ν₁) := by
    intro g
    refine ⟨(Langlands.QuotientIntegration.rightTranslate Γ g).continuous.measurable, ?_⟩
    have hcomm : (Langlands.QuotientIntegration.rightTranslate Γ g) ∘ E =
        E ∘ (LeftCosetSpace.rightTranslate
          (rationalSubgroup F G (V.comap e.hom)) (a.symm g)) := by
      funext q
      change LeftCosetSpace.rightTranslate Γ g (E q) = E
        (LeftCosetSpace.rightTranslate
          (rationalSubgroup F G (V.comap e.hom)) (a.symm g) q)
      have h := rationalQuotientIso_rightTranslate F e V (a.symm g) q
      change E (LeftCosetSpace.rightTranslate
          (rationalSubgroup F G (V.comap e.hom)) (a.symm g) q) =
        LeftCosetSpace.rightTranslate Γ (a (a.symm g)) (E q) at h
      simpa only [a.apply_symm_apply] using h.symm
    rw [Measure.map_map
      (Langlands.QuotientIntegration.rightTranslate Γ g).continuous.measurable
      E.continuous.measurable, hcomm, ← Measure.map_map E.continuous.measurable
      (LeftCosetSpace.continuous_rightTranslate
        (rationalSubgroup F G (V.comap e.hom)) (a.symm g)).measurable,
      (measurePreserving_rightTranslate_of_compactRationalQuotient F G
        (V.comap e.hom) (a.symm g)).map_eq]
  have hinv₂ : ∀ g : adelicPoints F H V,
      MeasurePreserving (Langlands.QuotientIntegration.rightTranslate Γ g) ν₂ ν₂ :=
    (compactCompatibleNormalizedRationalQuotientMeasure F H V).property.2.right_invariant
  obtain ⟨C, _, hC⟩ :=
    Langlands.QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient Γ
      (Γ.isClosed_of_isDiscrete hΓ) Measure.count (Measure.map E ν₁) ν₂
      (NeZero.ne _) (NeZero.ne _) hinv hinv₂
  have hmass := congrArg (fun M : Measure (RationalQuotient F H V) => M univ) hC
  have hmapmass : (Measure.map E ν₁) univ = 1 := measure_univ
  have hscalar : ENNReal.ofReal C = 1 := by simpa only [measure_univ, Measure.smul_apply,
    smul_eq_mul, mul_one, hmapmass] using hmass.symm
  exact ⟨E.continuous.measurable, by simpa only [hscalar, one_smul] using hC⟩

/-- The inverse of the constructed quotient map preserves the same intrinsic probabilities. -/
theorem measurePreserving_rationalQuotientIso_symm :
    MeasurePreserving (rationalQuotientIso F e V).symm
      (normalizedRationalQuotientHaarMeasure F H V)
      (normalizedRationalQuotientHaarMeasure F G (V.comap e.hom)) := by
  refine ⟨(rationalQuotientIso F e V).symm.continuous.measurable, ?_⟩
  rw [← (measurePreserving_rationalQuotientIso F e V).map_eq]
  exact (rationalQuotientIso F e V).toMeasurableEquiv.map_symm_map

/-- Absolute convergence is equivalent before and after the actual quotient change of variables. -/
theorem integrable_comp_rationalQuotientIso_iff (f : RationalQuotient F H V → ℂ) :
    Integrable (f ∘ rationalQuotientIso F e V)
        (normalizedRationalQuotientHaarMeasure F G (V.comap e.hom)) ↔
      Integrable f (normalizedRationalQuotientHaarMeasure F H V) :=
  (measurePreserving_rationalQuotientIso F e V).integrable_comp_emb
    (rationalQuotientIso F e V).toMeasurableEquiv.measurableEmbedding

/-- The quotient period is unchanged; its convergence is recorded separately by the
preceding equivalence. -/
theorem integral_comp_rationalQuotientIso (f : RationalQuotient F H V → ℂ) :
    (∫ q, f (rationalQuotientIso F e V q)
      ∂normalizedRationalQuotientHaarMeasure F G (V.comap e.hom)) =
      ∫ q, f q ∂normalizedRationalQuotientHaarMeasure F H V :=
  (measurePreserving_rationalQuotientIso F e V).integral_comp
    (rationalQuotientIso F e V).toMeasurableEquiv.measurableEmbedding f

end CompactMeasure

end Langlands.Global.AdelicSubgroupPoints
