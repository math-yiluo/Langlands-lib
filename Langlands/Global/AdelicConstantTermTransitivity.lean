import Langlands.Global.CompactQuotientSubgroupAverage
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure
import Langlands.Automorphic.GroupSchemeConstantTermConsequences
import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction

/-! # Nested normalized constant terms on actual adelic points

For subgroup functors `U ≤ V` whose actual principal quotients are compact,
if `U` is normalized by `V` on test schemes, averaging along `U` before taking
the constant term along `V` does not change the latter. Here the two integrals
use the intrinsic probability measures, not an unspecified Haar scalar.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Inclusion of the actual adelic points for a containment of subgroup functors. -/
def adelicInclusion {U V : SubgroupFunctor G} (h : U ≤ V) :
    adelicPoints F G U →* adelicPoints F G V := Subgroup.inclusion (h _)

@[simp] theorem adelicInclusion_coe {U V : SubgroupFunctor G} (h : U ≤ V)
    (x : adelicPoints F G U) : (adelicInclusion F G h x : AdelicGroupPoints F G) = x := rfl

/-- Subgroup inclusion preserves the actual principal images, by naturality. -/
theorem rationalSubgroup_le_comap_adelicInclusion {U V : SubgroupFunctor G} (h : U ≤ V) :
    rationalSubgroup F G U ≤ (rationalSubgroup F G V).comap (adelicInclusion F G h) := by
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨q.val, h _ q.2⟩, rfl⟩

section Conjugation

variable [IsAffine G.X.left] {U V : SubgroupFunctor G} (hUV : U.IsNormalizedBy V)

/-- Conjugation by an actual point of the normalizing subgroup. -/
def adelicNormalizerConj (x : adelicPoints F G V) :
    adelicPoints F G U ≃ₜ* adelicPoints F G U := by
  let a : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G :=
    { toMulEquiv := MulAut.conj (x : AdelicGroupPoints F G)
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
      continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }
  apply QuotientIntegration.subgroupAutomorphism _ a
  intro y
  change (x : AdelicGroupPoints F G) * y * (x : AdelicGroupPoints F G)⁻¹ ∈
    adelicPoints F G U ↔ y ∈ adelicPoints F G U
  constructor
  · intro hy
    have hy' : (x : AdelicGroupPoints F G)⁻¹ *
        ((x : AdelicGroupPoints F G) * y * (x : AdelicGroupPoints F G)⁻¹) *
          ((x : AdelicGroupPoints F G)⁻¹)⁻¹ ∈ adelicPoints F G U :=
      hUV _ _ _ ((adelicPoints F G V).inv_mem x.2) hy
    simpa [mul_assoc] using hy'
  · exact hUV _ _ _ x.2

@[simp] theorem adelicNormalizerConj_coe (x : adelicPoints F G V) (y : adelicPoints F G U) :
    (adelicNormalizerConj F G hUV x y : AdelicGroupPoints F G) =
      (x : AdelicGroupPoints F G) * y * (x : AdelicGroupPoints F G)⁻¹ := rfl

theorem adelicNormalizerConj_mem_rationalSubgroup_iff
    (q : rationalPoints F G V) (y : adelicPoints F G U) :
    adelicNormalizerConj F G hUV (rational F G V q) y ∈ rationalSubgroup F G U ↔
      y ∈ rationalSubgroup F G U := by
  have hforward : ∀ z : rationalPoints F G V, ∀ v ∈ rationalSubgroup F G U,
      adelicNormalizerConj F G hUV (rational F G V z) v ∈ rationalSubgroup F G U := by
    intro z v hv
    obtain ⟨r, rfl⟩ := hv
    refine ⟨⟨z.val * r.val * z.val⁻¹, hUV _ _ _ z.2 r.2⟩, ?_⟩
    apply Subtype.ext
    simp only [rational_coe, adelicNormalizerConj_coe, map_mul, map_inv]
  refine ⟨fun hy => ?_, hforward q y⟩
  have h := hforward q⁻¹ _ hy
  have hcancel : adelicNormalizerConj F G hUV (rational F G V q⁻¹)
      (adelicNormalizerConj F G hUV (rational F G V q) y) = y := by
    apply Subtype.ext
    simp [mul_assoc]
  exact hcancel ▸ h

end Conjugation

section Compact

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (U : SubgroupFunctor G)
  [hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G U)]

local instance normalizerSubgroupLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G U) :=
  hU.locallyCompactSpace

local instance normalizerQuotientBorelSpace : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

omit hU [CompactSpace (RationalQuotient F G U)] in
private theorem rationalSubgroup_count_isHaarMeasure :
    (Measure.count : Measure (rationalSubgroup F G U)).IsHaarMeasure := by
  let := LeftCosetSpace.isFiniteMeasureOnCompacts_count (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U)
  exact { toIsOpenPosMeasure := ⟨fun _ _ hs => Measure.count_ne_zero hs⟩ }

/-- A continuous automorphism preserving the actual principal subgroup preserves the
intrinsic normalized probability. -/
theorem measurePreserving_rationalQuotientAutomorphism
    (a : adelicPoints F G U ≃ₜ* adelicPoints F G U)
    (ha : ∀ x : adelicPoints F G U, a x ∈ rationalSubgroup F G U ↔
      x ∈ rationalSubgroup F G U) :
    MeasurePreserving (QuotientIntegration.quotientAutomorphism (rationalSubgroup F G U) a ha)
      (normalizedRationalQuotientHaarMeasure F G U) (normalizedRationalQuotientHaarMeasure F G U) := by
  let Γ := rationalSubgroup F G U
  have hd : IsDiscrete (Γ : Set (adelicPoints F G U)) := isDiscrete_rationalSubgroup F G U
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hd
  let : (Measure.count : Measure Γ).IsHaarMeasure := rationalSubgroup_count_isHaarMeasure F G U
  let : IsProbabilityMeasure (normalizedRationalQuotientHaarMeasure F G U) :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  let : (normalizedRationalQuotientHaarMeasure F G U).Regular :=
    (compactCompatibleNormalizedRationalQuotientMeasure F G U).property.2.regular
  exact LeftCosetSpace.measurePreserving_quotientAutomorphism_of_probability Γ
    (Γ.isClosed_of_isDiscrete hd) Measure.count _
    (measurePreserving_rightTranslate_of_compactRationalQuotient F G U) a ha

/-- The constant term for the intrinsic normalized measure on the actual rational quotient. -/
def normalizedConstantTerm (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) : ℂ :=
  constantTerm F G U (normalizedRationalQuotientHaarMeasure F G U) f g

omit [CompactSpace (RationalQuotient F G U)] in
/-- At a represented subgroup the descended integral equals the chosen-representative integral. -/
theorem normalizedConstantTerm_range_eq_subgroupConstantTerm
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    haveI := isClosed_adelicPoints_range F G j
    normalizedConstantTerm F G (SubgroupFunctor.range j) f g =
      AdelicGroupPoints.subgroupConstantTerm F j (evaluate F G f) g := by
  dsimp only [normalizedConstantTerm, constantTerm, AdelicGroupPoints.subgroupConstantTerm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by
    have hq : LeftCosetSpace.mk (rationalSubgroup F G (SubgroupFunctor.range j))
        (Quotient.out q) = q := Quotient.out_eq q
    exact congrArg (constantTermIntegrand F G (SubgroupFunctor.range j) f g) hq.symm)

/-- The normalized constant term is invariant under left translation by the adelic subgroup. -/
theorem normalizedConstantTerm_subgroup_mul (f : ContinuousRationalFunctions F G)
    (n : adelicPoints F G U) (g : AdelicGroupPoints F G) :
    normalizedConstantTerm F G U f ((n : AdelicGroupPoints F G) * g) =
      normalizedConstantTerm F G U f g :=
  constantTerm_subgroup_mul F G U (normalizedRationalQuotientHaarMeasure F G U) f n
    (measurePreserving_rightTranslate_of_compactRationalQuotient F G U n) g

/-- The normalized constant term is continuous in the ambient argument. -/
theorem continuous_normalizedConstantTerm (f : ContinuousRationalFunctions F G) :
    Continuous (normalizedConstantTerm F G U f) := by
  let m := normalizedRationalQuotientHaarMeasure F G U
  let : IsProbabilityMeasure m := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  have hc : Continuous (Function.uncurry (constantTermIntegrand F G U f)) := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (LeftCosetSpace.isOpenQuotientMap_mk (rationalSubgroup F G U))).continuous_comp_iff]
    exact f.property.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support («μ» := m) isCompact_univ hc.continuousOn (by simp)

/-- Rational points of a normalizing subgroup preserve the normalized constant term. -/
theorem normalizedConstantTerm_rationalNormalizer_mul {V : SubgroupFunctor G}
    (hUV : U.IsNormalizedBy V) (q : rationalPoints F G V)
    (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    normalizedConstantTerm F G U f (AdelicGroupPoints.rational F G q.val * g) =
      normalizedConstantTerm F G U f g := by
  let Δ := rationalSubgroup F G U
  let a := adelicNormalizerConj F G hUV (rational F G V q⁻¹)
  have ha := adelicNormalizerConj_mem_rationalSubgroup_iff F G hUV q⁻¹
  let e := QuotientIntegration.quotientAutomorphism Δ a ha
  have he := measurePreserving_rationalQuotientAutomorphism F G U a ha
  have hfun : constantTermIntegrand F G U f (AdelicGroupPoints.rational F G q.val * g) =
      constantTermIntegrand F G U f g ∘ e := by
    funext x
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective Δ x
    change evaluate F G f ((n : AdelicGroupPoints F G) * (AdelicGroupPoints.rational F G q.val * g)) =
      evaluate F G f ((a n : AdelicGroupPoints F G) * g)
    have hmul : (n : AdelicGroupPoints F G) * (AdelicGroupPoints.rational F G q.val * g) =
        AdelicGroupPoints.rational F G q.val * ((a n : AdelicGroupPoints F G) * g) := by
      simp [a, mul_assoc]
    rw [hmul]
    exact f.val.property q.val _
  unfold normalizedConstantTerm constantTerm
  rw [hfun]
  exact he.integral_comp e.measurableEmbedding _

end Compact

section Nested

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {U V : SubgroupFunctor G} (h : U ≤ V) (hUV : U.IsNormalizedBy V)
  [hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [hV : IsClosed (adelicPoints F G V : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G U)] [CompactSpace (RationalQuotient F G V)]

local instance outerSubgroupLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G V) :=
  hV.locallyCompactSpace

local instance innerQuotientBorelSpace : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

local instance outerQuotientBorelSpace : BorelSpace (RationalQuotient F G V) :=
  rationalQuotientBorelSpace F G V

include h hUV in
/-- On the actual compact radical quotients, taking the `V` constant term after the
`U` constant term is the same as taking just the `V` constant term. The iterated
integral is written on representatives because the `U` constant term is not a
function on the ambient rational quotient in general. -/
theorem integral_normalizedConstantTerm_eq_of_isNormalizedBy
    (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    (∫ x : RationalQuotient F G V,
      normalizedConstantTerm F G U f
        (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g)
        ∂normalizedRationalQuotientHaarMeasure F G V) = normalizedConstantTerm F G V f g := by
  let Γ := rationalSubgroup F G V
  let Δ := rationalSubgroup F G U
  let j := adelicInclusion F G h
  let mU := normalizedRationalQuotientHaarMeasure F G U
  let mV := normalizedRationalQuotientHaarMeasure F G V
  let fG := constantTermIntegrand F G V f g
  have hΓ : IsDiscrete (Γ : Set (adelicPoints F G V)) := isDiscrete_rationalSubgroup F G V
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let : (Measure.count : Measure Γ).IsHaarMeasure := rationalSubgroup_count_isHaarMeasure F G V
  let : IsProbabilityMeasure mU := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  let : IsProbabilityMeasure mV := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let : mV.Regular :=
    (compactCompatibleNormalizedRationalQuotientMeasure F G V).property.2.regular
  have hj : Δ ≤ Γ.comap j := rationalSubgroup_le_comap_adelicInclusion F G h
  have hjc : Continuous j := continuous_subtype_val.subtype_mk _
  have hconj := LeftCosetSpace.subgroupAverageConjugation Γ Δ j hj mU (by
    rintro ⟨_, q, rfl⟩
    let a := adelicNormalizerConj F G hUV (rational F G V q⁻¹)
    have ha := adelicNormalizerConj_mem_rationalSubgroup_iff F G hUV q⁻¹
    refine ⟨a, ha, measurePreserving_rationalQuotientAutomorphism F G U a ha, fun n => ?_⟩
    apply Subtype.ext
    change (a n : AdelicGroupPoints F G) =
      (rational F G V q : AdelicGroupPoints F G)⁻¹ * n * (rational F G V q : AdelicGroupPoints F G)
    simp [a])
  have hi := LeftCosetSpace.integral_compactSubgroupAverage Γ Δ j hj hjc mU hconj
    (Γ.isClosed_of_isDiscrete hΓ) Measure.count mV
    (measurePreserving_rightTranslate_of_compactRationalQuotient F G V)
    (continuous_constantTermIntegrand F G V f g)
  refine Eq.trans ?_ hi
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have hx : LeftCosetSpace.mk Γ (Quotient.out x) = x := Quotient.out_eq x
    rw [← hx, LeftCosetSpace.compactSubgroupAverage_mk, hx]
    change (∫ y, constantTermIntegrand F G U f
      (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g) y ∂mU) =
        ∫ y, LeftCosetSpace.subgroupFiberEval Γ Δ j hj fG (Quotient.out x) y ∂mU
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective Δ y
      exact congrArg (evaluate F G f) (mul_assoc _ _ _).symm))

end Nested

end Langlands.Global.AdelicSubgroupPoints

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "rad(" J ")" => SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)

omit [NumberField F] in
/-- The supplied geometric radical has the canonical standard image on all test schemes. -/
theorem range_radical_eq_standardUnipotent (J : Idx) :
    rad(J) = standardUnipotent 𝓕.i 𝓕.ν J.1 := by
  let := 𝓕.connectedReductive.smooth
  let := (𝓕.isCompatible J).parabolic.isClosedSubgroup.mono
  let := ((𝓕.isCompatible J).levi.isClosedSubgroup.comp
    (𝓕.isCompatible J).parabolic.isClosedSubgroup).mono
  obtain ⟨z, hz, hP, hM⟩ := (𝓕.isCompatible J).realization
  have h := Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
    (CommGroupScheme.groupHom z ≫ 𝓕.i) (p := 𝓕.p J) (z := 𝓕.l J ≫ 𝓕.p J)
    ⟨Over.mono_of_mono_left _, hP⟩ ⟨Over.mono_of_mono_left _, hM⟩
    (𝓕.isCompatible J).levi.isConnectedReductive (𝓕.isUnipotentRadical J)
  have hstd := (standardCocharacter F G 𝓕.connectedReductive 𝓕.T 𝓕.i
    𝓕.maximalSplit 𝓕.ν 𝓕.generic J.1 J.2).2 z hz
  exact h.trans hstd.2.2.symm

omit [NumberField F] in
/-- In a nested pair `Q ≤ P`, the smaller radical is `U_P`. -/
theorem radical_le_of_le {Q P : Idx} (hQP : Q ≤ P) : rad(P) ≤ rad(Q) := by
  rw [𝓕.range_radical_eq_standardUnipotent, 𝓕.range_radical_eq_standardUnipotent]
  exact ((standardParabolicOrder F G 𝓕.connectedReductive 𝓕.T 𝓕.i
    𝓕.maximalSplit 𝓕.ν 𝓕.generic).1 Q.1 P.1 Q.2 P.2).2 hQP |>.2

omit [NumberField F] in
/-- The larger radical `U_Q` normalizes `U_P` since it lies in `P`. -/
theorem radical_isNormalizedBy_of_le {Q P : Idx} (hQP : Q ≤ P) :
    rad(P).IsNormalizedBy rad(Q) := by
  rw [𝓕.range_radical_eq_standardUnipotent, 𝓕.range_radical_eq_standardUnipotent]
  intro X v u hv hu
  have hvQ := standardUnipotent_le_standardParabolic 𝓕.i 𝓕.ν Q.1 X hv
  have hvP := ((standardParabolicOrder F G 𝓕.connectedReductive 𝓕.T 𝓕.i
    𝓕.maximalSplit 𝓕.ν 𝓕.generic).1 Q.1 P.1 Q.2 P.2).1.mp hQP X hvQ
  exact StandardLeviIntersection.conj_mem_standardUnipotent 𝓕.i 𝓕.ν hvP hu

/-- The actual rational quotient of each standard unipotent radical is compact. -/
theorem compactSpace_radicalRationalQuotient (J : Idx) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F G rad(J)) := by
  have h := (𝓕.isUnipotentRadical J).isGeometricUnipotentRadical
  exact AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F
    (𝓕.iU J ≫ 𝓕.p J) h.2.1 h.2.2.1 h.2.2.2.1

/-- Transitivity for the existing standard-family constant term on continuous
rational-invariant inputs. This is `C_Q (C_P f) = C_Q f` for `Q ≤ P`. -/
theorem constantTerm_constantTerm_of_le {Q P : Idx} (hQP : Q ≤ P)
    (f : ContinuousRationalFunctions F G) :
    𝓕.constantTerm Q (𝓕.constantTerm P (evaluate F G f)) =
      𝓕.constantTerm Q (evaluate F G f) := by
  open AdelicSubgroupPoints in
  funext g
  let : IsClosed (adelicPoints F G rad(P) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU P ≫ 𝓕.p P)
  let : IsClosed (adelicPoints F G rad(Q) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient P
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  change AdelicGroupPoints.subgroupConstantTerm F (𝓕.iU Q ≫ 𝓕.p Q)
    (AdelicGroupPoints.subgroupConstantTerm F (𝓕.iU P ≫ 𝓕.p P) (evaluate F G f)) g =
      AdelicGroupPoints.subgroupConstantTerm F (𝓕.iU Q ≫ 𝓕.p Q) (evaluate F G f) g
  rw [← normalizedConstantTerm_range_eq_subgroupConstantTerm F G (𝓕.iU Q ≫ 𝓕.p Q) f g]
  have hp : AdelicGroupPoints.subgroupConstantTerm F (𝓕.iU P ≫ 𝓕.p P) (evaluate F G f) =
      normalizedConstantTerm F G rad(P) f :=
    funext (fun x => (normalizedConstantTerm_range_eq_subgroupConstantTerm F G
      (𝓕.iU P ≫ 𝓕.p P) f x).symm)
  rw [hp]
  exact integral_normalizedConstantTerm_eq_of_isNormalizedBy F G (𝓕.radical_le_of_le hQP)
    (𝓕.radical_isNormalizedBy_of_le hQP) f g

end Langlands.Global.StandardParabolicFamily
