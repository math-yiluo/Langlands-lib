import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.EisensteinConstantTerm.Reduction
import Langlands.Global.RelativelyCompactFundamentalDomainProof
import Langlands.Automorphic.GroupSchemeManifoldSmooth
import Langlands.Geometry.Manifold.SmoothGroupDifferential
import Langlands.Analysis.CompactManifoldVectorIntegral

/-! # Archimedean differentiation of the unipotent constant term -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff ENNReal

namespace Langlands.Global

open AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Geometry.Manifold Langlands.Analysis

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {d : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "I∞" => 𝓘(ℝ, smoothModel F d)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "V" => SubgroupFunctor.range j
local notation "H" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "ν" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
local notation "m" => map F U G j

/-- The right-orbit derivative in an actual archimedean tangent direction. -/
def adelicDirectionalValue (X : smoothModel F d) (f : A → ℂ) (x : A) : ℂ :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  mvfderiv I∞ (fun t : G∞ => f (x * ofInfinite F G t)) 1 X

omit [LocallyOfFiniteType G.X.hom] in
/-- The adelic right-orbit derivative on a fixed finite slice. -/
theorem adelicDirectionalValue_pair (X : smoothModel F d) (f : A → ℂ)
    (a : G∞) (b : Gf) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    adelicDirectionalValue hG X f (pair F G a b) =
      groupDirectionalValue I∞ X (fun y => f (pair F G y b)) a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  simp only [adelicDirectionalValue, groupDirectionalValue, ofInfinite_eq_pair, pair_mul, mul_one]

/-- The actual normalized constant term is archimedean-smooth and commutes with the
right-orbit derivative, for continuous functions smooth on the infinite slices and fixed
by a given open finite level and the rational unipotent subgroup. -/
def AdelicUnipotentConstantTermDifferentiationStatement : Prop :=
  Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
  ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (f : A → ℂ), Continuous f →
  (∀ b : Gf, ContMDiff I∞ IC ∞ (fun y : G∞ => f (pair F G y b))) →
  (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) →
  (∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x) →
  (∀ X : smoothModel F d, Continuous (adelicDirectionalValue hG X f) ∧
    (∀ b : Gf, ContMDiff I∞ IC ∞ (fun y : G∞ => adelicDirectionalValue hG X f (pair F G y b))) ∧
    (∀ (q : RationalGroupPoints F U) x,
      adelicDirectionalValue hG X f (m (rational F U q) * x) = adelicDirectionalValue hG X f x) ∧
    (∀ l ∈ L, ∀ x, adelicDirectionalValue hG X f (x * ofFinite F G l) = adelicDirectionalValue hG X f x)) ∧
  ∀ b : Gf, ContMDiff I∞ IC ∞ (fun y : G∞ => subgroupConstantTerm F j f (pair F G y b)) ∧
    ∀ (X : smoothModel F d) (a : G∞),
      groupDirectionalValue I∞ X (fun y : G∞ => subgroupConstantTerm F j f (pair F G y b)) a =
        subgroupConstantTerm F j (adelicDirectionalValue hG X f) (pair F G a b)

theorem adelicUnipotentConstantTermDifferentiation :
    AdelicUnipotentConstantTermDifferentiationStatement j hG := by
  intro hUs hconn hu L hLo
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let : IsManifold I∞ ∞ G∞ := smoothIsManifold F G hG
  let := smoothLieGroup F G hG
  let (v : InfinitePlace F) : FiniteDimensional ℝ v.Completion := inferInstance
  intro f hf hfS hfR hfL
  let T := Gf ⧸ L
  let Z := Fin 0 → ℝ
  let : DiscreteTopology T := QuotientGroup.discreteTopology hLo
  let : ChartedSpace Z T := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ T := IsManifold.of_discreteTopology ∞
  let : ChartedSpace (smoothModel F d × Z) (G∞ × T) := prodChartedSpace _ _ _ _
  let : IsManifold 𝓘(ℝ, smoothModel F d × Z) ∞ (G∞ × T) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := I∞) (I' := 𝓘(ℝ, Z)) G∞ T
  let π : Gf → T := QuotientGroup.mk
  let fS (b : Gf) (y : G∞) := f (pair F G y b)
  have hfS_shift (b : Gf) : fS (π b).out = fS b := by
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (s := L) b
    funext y
    change f (pair F G y (π b).out) = f (pair F G y b)
    rw [show (π b).out = b * l.val from hl]
    simpa only [ofFinite_eq_pair, pair_mul, mul_one] using hfL l.val l.property (pair F G y b)
  have hdL (X : smoothModel F d) (l : Gf) (hl : l ∈ L) (x : A) :
      adelicDirectionalValue hG X f (x * ofFinite F G l) = adelicDirectionalValue hG X f x := by
    unfold adelicDirectionalValue
    apply congrArg (fun w : G∞ → ℂ => mvfderiv I∞ w 1 X)
    funext t
    rw [mul_assoc, ← (factors_commute F G t l).eq, ← mul_assoc, hfL l hl]
  have hdR (X : smoothModel F d) (q : RationalGroupPoints F U) (x : A) :
      adelicDirectionalValue hG X f (m (rational F U q) * x) = adelicDirectionalValue hG X f x := by
    unfold adelicDirectionalValue
    apply congrArg (fun w : G∞ → ℂ => mvfderiv I∞ w 1 X)
    funext t
    rw [mul_assoc, hfR q]
  have hdS (X : smoothModel F d) (b : Gf) :
      ContMDiff I∞ IC ∞ (fun y : G∞ => adelicDirectionalValue hG X f (pair F G y b)) := by
    simp only [adelicDirectionalValue_pair]
    exact contMDiff_groupDirectionalValue I∞ X (hfS b)
  have hdC (X : smoothModel F d) : Continuous (adelicDirectionalValue hG X f) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hloc : ∀ᶠ t : A in 𝓝 x, π (finite F G t) = π (finite F G x) :=
      ((QuotientGroup.continuous_mk.comp (finite F G).continuous).tendsto x).eventually
        ((_root_.isOpen_discrete ({π (finite F G x)} : Set T)).mem_nhds (mem_singleton _))
    have hEq : adelicDirectionalValue hG X f =ᶠ[𝓝 x]
        fun t => groupDirectionalValue I∞ X (fS (finite F G x)) (infinite F G t) := by
      filter_upwards [hloc] with t ht
      conv_lhs => rw [← pair_projections F G t, adelicDirectionalValue_pair]
      change groupDirectionalValue I∞ X (fS (finite F G t)) (infinite F G t) = _
      rw [← hfS_shift (finite F G t), ht, hfS_shift]
    exact (((contMDiff_groupDirectionalValue I∞ X (hfS (finite F G x))).continuous.comp
      (infinite F G).continuous).continuousAt).congr hEq.symm
  refine ⟨fun X => ⟨hdC X, hdS X, hdR X, hdL X⟩, ?_⟩
  let : IsClosed (H : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace H := (show IsClosed (H : Set A) from inferInstance).locallyCompactSpace
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hUs hconn hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure ν := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  obtain ⟨K, hK, hKcov⟩ := EisensteinConstantTerm.exists_isCompact_mul_mem Γ
  obtain ⟨s, hs, hsc, _, _, hsPres, hsFinite, _⟩ := LeftCosetSpace.relativelyCompactFundamentalDomain
    Γ (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G V) K hK (by
      intro x
      obtain ⟨r, hr, y, hy, rfl⟩ := hKcov x
      exact ⟨⟨r⁻¹, Subgroup.inv_mem Γ hr⟩, by simpa using hy⟩)
  let mh : Measure H := Measure.haar
  let c := AdelicSubgroupPoints.quotientMassNormalizer F G V
  let m₀ : Measure H := c • mh
  let C := closure s
  have hCm : MeasurableSet C := isClosed_closure.measurableSet
  let : CompactSpace C := isCompact_iff_compactSpace.mp hsc
  have hm₀s : m₀ s ≠ (⊤ : ℝ≥0∞) := by
    change (c • mh) s ≠ ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G V) (hsFinite mh).ne
  let : IsFiniteMeasure (m₀.restrict s) := isFiniteMeasure_restrict.mpr hm₀s
  let mC : Measure C := (m₀.restrict s).comap Subtype.val
  have hpres : MeasurePreserving (LeftCosetSpace.mk Γ) (m₀.restrict s) ν := by
    simpa only [m₀, Measure.restrict_smul, AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
      AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure, mh, c]
        using (hsPres mh).smul_measure c
  have hIntegral (w : A → ℂ) (hw : Continuous w)
      (hwR : ∀ (q : RationalGroupPoints F U) x, w (m (rational F U q) * x) = w x) (x : A) :
      subgroupConstantTerm F j w x = ∫ z : C, w (z.val.val * x) ∂mC := by
    let wQ := LeftCosetSpace.lift Γ (fun y : H => w (y.val * x)) (fun r y => by
      obtain ⟨r₀, hr₀⟩ := (mem_rationalSubgroup_range_iff j r.val).mp r.2
      change w ((r.val.val * y.val) * x) = _
      rw [← hr₀, mul_assoc]
      exact hwR r₀ (y.val * x))
    have hwQ : Continuous wQ :=
      (LeftCosetSpace.continuous_iff Γ).mpr (hw.comp (continuous_subtype_val.mul continuous_const))
    have he : (fun q : Q => w ((Quotient.out q : H).val * x)) = wQ :=
      funext fun q => congrArg wQ (Quotient.out_eq q)
    change (∫ q : Q, w ((Quotient.out q : H).val * x) ∂ν) = _
    rw [he, ← hpres.map_eq, integral_map hpres.measurable.aemeasurable]
    · rw [show (∫ z : C, w (z.val.val * x) ∂mC) =
        ∫ z in C, w (z.val * x) ∂m₀.restrict s from
          integral_subtype_comap hCm (fun z : H => w (z.val * x))]
      rw [Measure.restrict_restrict hCm, Set.inter_eq_right.mpr subset_closure]
      rfl
    · rw [hpres.map_eq]
      exact hwQ.aestronglyMeasurable
  intro b
  let e : C(C, G∞ × T) := ⟨fun z => (infinite F G z.val.val, π (finite F G z.val.val * b)), by
    have ht : Continuous (fun z : C => z.val.val) := continuous_subtype_val.comp continuous_subtype_val
    exact ((infinite F G).continuous.comp ht).prodMk
      (QuotientGroup.continuous_mk.comp (((finite F G).continuous.comp ht).mul continuous_const))⟩
  let k (p : G∞ × (G∞ × T)) : ℂ := fS p.2.2.out (p.2.1 * p.1)
  have hk : ContMDiff (ModelWithCorners.prod I∞ 𝓘(ℝ, smoothModel F d × Z)) IC ∞ k := by
    rw [modelWithCornersSelf_prod]
    intro p
    have hk' := (hfS p.2.2.out).comp
      ((contMDiff_fst.comp contMDiff_snd).mul contMDiff_fst :
        ContMDiff (ModelWithCorners.prod I∞ (ModelWithCorners.prod I∞ 𝓘(ℝ, Z))) I∞ ∞ (fun r : G∞ × (G∞ × T) => r.2.1 * r.1))
    apply (hk' p).congr_of_eventuallyEq
    have hc : Continuous (fun r : G∞ × (G∞ × T) => r.2.2) := continuous_snd.comp continuous_snd
    have hp : ({p.2.2} : Set T) ∈ 𝓝 p.2.2 :=
      (_root_.isOpen_discrete _).mem_nhds (mem_singleton _)
    filter_upwards [(hc.tendsto p).eventually hp] with r hr
    change r.2.2 = p.2.2 at hr
    change fS r.2.2.out (r.2.1 * r.1) = fS p.2.2.out (r.2.1 * r.1)
    rw [hr]
  have hker (a : G∞) (z : C) : k (a, e z) = f (z.val.val * pair F G a b) := by
    change fS (π (finite F G z.val.val * b)).out (infinite F G z.val.val * a) = _
    rw [hfS_shift]
    change f (pair F G (infinite F G z.val.val * a) (finite F G z.val.val * b)) = _
    apply congrArg f
    apply (split F G).injective
    simp only [split_apply, map_mul, infinite_pair, finite_pair]
    rfl
  have heval : (fun y : G∞ => subgroupConstantTerm F j f (pair F G y b)) =
      fun y : G∞ => ∫ z : C, (1 : C(C, ℂ)) z • k (y, e z) ∂mC := by
    funext y
    rw [hIntegral f hf hfR]
    simp only [ContinuousMap.one_apply, one_smul, hker]
  refine ⟨?_, fun X a => ?_⟩
  · rw [heval]
    exact (compactManifoldVectorIntegral C (smoothModel F d) G∞
      (smoothModel F d × Z) (G∞ × T) ℂ mC 1 e k hk).2.1
  let ka (p : G∞ × (G∞ × T)) := k (a * p.1, p.2)
  have hka : ContMDiff (ModelWithCorners.prod I∞ 𝓘(ℝ, smoothModel F d × Z)) IC ∞ ka :=
    hk.comp ((contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd)
  have hder := (compactManifoldVectorIntegral C (smoothModel F d) G∞
    (smoothModel F d × Z) (G∞ × T) ℂ mC 1 e ka hka).2.2.2 1 X
  rw [heval, hIntegral _ (hdC X) (hdR X)]
  change (mfderiv I∞ IC (fun t => ∫ z : C, (1 : C(C, ℂ)) z • ka (t, e z) ∂mC) 1 X : ℂ) = _
  refine hder.trans (integral_congr_ae (Eventually.of_forall ?_))
  intro z
  simp only [ContinuousMap.one_apply, one_smul]
  have hz : (fun t : G∞ => ka (t, e z)) = (fun t => f (z.val.val * pair F G (a * t) b)) :=
    funext fun t => hker (a * t) z
  rw [hz]
  change (mfderiv I∞ IC (fun t => f (z.val.val * pair F G (a * t) b)) 1 X : ℂ) =
    adelicDirectionalValue hG X f (z.val.val * pair F G a b)
  unfold adelicDirectionalValue
  apply congrArg (fun w : G∞ → ℂ => mfderiv I∞ IC w 1 X)
  funext t
  rw [mul_assoc, ofInfinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]

end Langlands.Global
