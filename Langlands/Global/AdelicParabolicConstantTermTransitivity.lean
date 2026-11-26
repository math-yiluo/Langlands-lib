import Langlands.Global.AdelicParabolicCuspidalVanishingReduction
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicStandardConstantTerm

/-! # Transitivity of constant terms on parabolic quotients

For standard parabolics `Q' ⊆ Q ⊆ R` and a continuous function `f` on `G(𝔸)` that is left
invariant under `U_R(𝔸) M_R(F)`, the constant term along `Q'` of the constant term along `Q`
of `f` is the constant term of `f` along `Q'` (Bernstein–Lapid §6.2: `C_{Q,Q'} ∘ C_{R,Q} =
C_{R,Q'}`). The Library's `constantTerm_constantTerm_of_le` treats `G(F)`-invariant inputs; here
only invariance under the rational points of the larger radical is used. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- For a function on `G(𝔸)` invariant under the rational points of `V`, the function
`n ↦ f(n g)` on `V(𝔸)`, descended to `V(F) \ V(𝔸)`. -/
def invariantIntegrand (V : SubgroupFunctor G) (f : AdelicGroupPoints F G → ℂ)
    (hf : ∀ q : rationalPoints F G V, ∀ x : AdelicGroupPoints F G,
      f (AdelicGroupPoints.rational F G q.val * x) = f x)
    (g : AdelicGroupPoints F G) : RationalQuotient F G V → ℂ :=
  LeftCosetSpace.lift (rationalSubgroup F G V) (fun n => f ((n : AdelicGroupPoints F G) * g)) (by
    rintro ⟨_, q, rfl⟩ n
    change f ((AdelicGroupPoints.rational F G q.val * (n : AdelicGroupPoints F G)) * g) = _
    rw [mul_assoc]
    exact hf q _)

theorem invariantIntegrand_mk (V : SubgroupFunctor G) (f : AdelicGroupPoints F G → ℂ)
    (hf : ∀ q : rationalPoints F G V, ∀ x : AdelicGroupPoints F G,
      f (AdelicGroupPoints.rational F G q.val * x) = f x)
    (g : AdelicGroupPoints F G) (n : adelicPoints F G V) :
    invariantIntegrand V f hf g (LeftCosetSpace.mk (rationalSubgroup F G V) n) =
      f ((n : AdelicGroupPoints F G) * g) := rfl

theorem invariantIntegrand_out (V : SubgroupFunctor G) (f : AdelicGroupPoints F G → ℂ)
    (hf : ∀ q : rationalPoints F G V, ∀ x : AdelicGroupPoints F G,
      f (AdelicGroupPoints.rational F G q.val * x) = f x)
    (g : AdelicGroupPoints F G) (x : RationalQuotient F G V) :
    invariantIntegrand V f hf g x =
      f (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g) := by
  conv_lhs => rw [← Quotient.out_eq x]
  rfl

theorem continuous_invariantIntegrand [IsAffine G.X.left] (V : SubgroupFunctor G)
    {f : AdelicGroupPoints F G → ℂ}
    (hc : Continuous f)
    (hf : ∀ q : rationalPoints F G V, ∀ x : AdelicGroupPoints F G,
      f (AdelicGroupPoints.rational F G q.val * x) = f x)
    (g : AdelicGroupPoints F G) : Continuous (invariantIntegrand V f hf g) :=
  (LeftCosetSpace.continuous_iff (rationalSubgroup F G V)).mpr
    (hc.comp (continuous_subtype_val.mul continuous_const))

section Nested

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {U V : SubgroupFunctor G} (h : U ≤ V) (hUV : U.IsNormalizedBy V)
  [hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [hV : IsClosed (adelicPoints F G V : Set (AdelicGroupPoints F G))]
  [CompactSpace (RationalQuotient F G U)] [CompactSpace (RationalQuotient F G V)]

local instance invariantOuterLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G V) :=
  hV.locallyCompactSpace

local instance invariantInnerBorelSpace : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

local instance invariantOuterBorelSpace : BorelSpace (RationalQuotient F G V) :=
  rationalQuotientBorelSpace F G V

omit hV [CompactSpace (RationalQuotient F G V)] in
private theorem count_isHaarMeasure_rationalSubgroup :
    (Measure.count : Measure (rationalSubgroup F G V)).IsHaarMeasure := by
  let := LeftCosetSpace.isFiniteMeasureOnCompacts_count (rationalSubgroup F G V)
    (isDiscrete_rationalSubgroup F G V)
  exact { toIsOpenPosMeasure := ⟨fun _ _ hs => Measure.count_ne_zero hs⟩ }

include h hUV in
/-- Iterated constant terms along `U ≤ V`, with `U` normalized by `V`, for a continuous function
invariant under the rational points of `V`, written with chosen representatives. -/
theorem integral_iterated_invariantIntegrand (f : AdelicGroupPoints F G → ℂ)
    (hc : Continuous f)
    (hf : ∀ q : rationalPoints F G V, ∀ x : AdelicGroupPoints F G,
      f (AdelicGroupPoints.rational F G q.val * x) = f x)
    (g : AdelicGroupPoints F G) :
    (∫ x : RationalQuotient F G V,
      (∫ y : RationalQuotient F G U,
        f (((Quotient.out y : adelicPoints F G U) : AdelicGroupPoints F G) *
          (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g))
        ∂normalizedRationalQuotientHaarMeasure F G U)
      ∂normalizedRationalQuotientHaarMeasure F G V) =
      ∫ x : RationalQuotient F G V,
        f (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g)
        ∂normalizedRationalQuotientHaarMeasure F G V := by
  let Γ := rationalSubgroup F G V
  let Δ := rationalSubgroup F G U
  let j := adelicInclusion F G h
  let mU := normalizedRationalQuotientHaarMeasure F G U
  let mV := normalizedRationalQuotientHaarMeasure F G V
  let fG := invariantIntegrand V f hf g
  have hΓ : IsDiscrete (Γ : Set (adelicPoints F G V)) := isDiscrete_rationalSubgroup F G V
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_rationalSubgroup
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
    (continuous_invariantIntegrand V hc hf g)
  have hrhs : (∫ x : RationalQuotient F G V,
      f (((Quotient.out x : adelicPoints F G V) : AdelicGroupPoints F G) * g) ∂mV) =
      ∫ x, fG x ∂mV :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      (invariantIntegrand_out V f hf g x).symm)
  rw [hrhs, ← hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have hx : LeftCosetSpace.mk Γ (Quotient.out x) = x := Quotient.out_eq x
    rw [← hx, LeftCosetSpace.compactSubgroupAverage_mk, hx]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      conv_rhs => rw [← Quotient.out_eq y]
      change _ = fG (LeftCosetSpace.mk Γ (j (Quotient.out y) * Quotient.out x))
      exact congrArg f (mul_assoc _ _ _).symm))

end Nested

end Langlands.Global.AdelicSubgroupPoints

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "rad(" J ")" => SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)

/-- For `Q ⊆ R`, the rational points of `U_Q` lie in `U_R(𝔸) M_R(F)`. -/
theorem rationalImage_radical_le_parabolicQuotientSubgroup {Q R : Idx} (hQR : Q ≤ R) :
    rationalImage F (𝓕.iU Q ≫ 𝓕.p Q) ≤
      parabolicQuotientSubgroup F (𝓕.p R) (𝓕.iU R) (𝓕.l R) := by
  have hle : rad(Q) ≤ SubgroupFunctor.range (𝓕.p R) :=
    (SubgroupFunctor.range_comp_le _ _).trans ((𝓕.le_iff_range_le Q R).mp hQR)
  let : IsClosedImmersion (𝓕.p R).hom.hom.left := (𝓕.isCompatible R).parabolic.isClosedSubgroup
  have hcomp := SubgroupFunctor.rangeFactor_comp (𝓕.iU Q ≫ 𝓕.p Q) (𝓕.p R) hle
  rw [← hcomp]
  exact (rationalImage_comp_le _ _).trans (rationalImage_le_parabolicQuotientSubgroup _ _ _
    (𝓕.isCompatible R).levi (𝓕.isUnipotentRadical R))

/-- If `Q ≤ P ≤ R`, taking the `Q` constant term of the `P` constant term of a continuous
function on the `R` parabolic quotient gives its `Q` constant term. -/
theorem constantTerm_constantTerm_of_parabolicQuotient {Q P R : Idx} (hQP : Q ≤ P) (hPR : P ≤ R)
    {f : AdelicGroupPoints F G → ℂ} (hf : Continuous f)
    (hInv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (𝓕.p R) (𝓕.iU R) (𝓕.l R)) f) :
    𝓕.constantTerm Q (𝓕.constantTerm P f) = 𝓕.constantTerm Q f :=
  𝓕.constantTerm_constantTerm_of_le_of_rationalParabolicInvariant hQP hf
    (𝓕.isLeftInvariantUnder_rationalImage_of_le (hQP.trans hPR) hInv)

end Langlands.Global.StandardParabolicFamily
