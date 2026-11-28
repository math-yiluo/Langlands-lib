import Langlands.Global.AdelicUnipotentFundamentalMeasure
import Langlands.Global.AdelicNormOneFamilyDecay
import Langlands.Global.AdelicSubgroupNormOne

/-! # Constant terms commute with norm-one derivatives, in integrated form

The normalized constant term along a closed smooth connected unipotent subgroup `U` preserves the
integrated derivative identity `IsNormOnePathDerivative`: if `f'` gives the derivatives of `f` along
smooth paths of `G(F∞)¹` at norm-one points, then the constant terms of `f'` give those of the
constant term of `f`. The constant term of a jointly measurable family of continuous functions is
jointly measurable. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj ENNReal Manifold ContDiff

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme Langlands.Analysis
  Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

/-- **Integrability against the fundamental measure.** Continuous functions on `U(𝔸)` are
integrable for a finite measure concentrated on a compact set. -/
theorem integrable_of_continuous_of_ae_mem {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν] {C : Set Y}
    (hC : IsCompact C) (hT : ∀ᵐ h ∂ν, h ∈ C) {φ : Y → ℂ} (hφ : Continuous φ) : Integrable φ ν := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hφ.continuousOn
  refine Integrable.of_bound hφ.aestronglyMeasurable M ?_
  filter_upwards [hT] with h hh using hM h hh

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  {d e : ℕ} {hG : SmoothOfRelativeDimension d G.X.hom}

local notation "A" => AdelicGroupPoints F G
local notation "V" => SubgroupFunctor.range j
local notation "H" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "m" => map F U G j

/-- Points of `U(𝔸)` are norm-one points of `G(𝔸)`. -/
theorem unipotent_adelicPoints_mem_normOne [Smooth U.X.hom] (hconn : ConnectedSpace U.X.left)
    (hu : IsUnipotent U) (h : H) : h.val ∈ normOneSubgroup F G := by
  let : IsClosed (H : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j inferInstance hconn hu
  exact AdelicSubgroupPoints.adelicPoints_le_normOneSubgroup F G V h.property

/-- **Constant terms preserve the integrated derivative identity.** -/
theorem isNormOnePathDerivative_subgroupConstantTerm [Smooth U.X.hom]
    (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U) (At : NormOneLieAtlas F G hG e)
    {f : A → ℂ} {f' : Fin e → A → ℂ} (hf : Continuous f) (hf' : ∀ l, Continuous (f' l))
    (hfR : ∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x)
    (hf'R : ∀ l (q : RationalGroupPoints F U) x, f' l (m (rational F U q) * x) = f' l x)
    (hder : IsNormOnePathDerivative At f f') :
    IsNormOnePathDerivative At (subgroupConstantTerm F j f)
      (fun l => subgroupConstantTerm F j (f' l)) := by
  obtain ⟨ν, C, hν, hC, hνC, hrep⟩ := exists_unipotentFundamentalMeasure j hconn hu
  have hT : ∀ᵐ h ∂ν, h ∈ C := by
    rw [ae_iff]
    exact hνC
  let := At.chartedSpace
  let := At.lieGroup
  intro y hy c Vel hc hV hVc
  have hcc : Continuous c := hc.continuous
  have hpath : Continuous fun t : ℝ => y * ofInfinite F G (c t) :=
    continuous_const.mul ((ofInfinite F G).continuous.comp (continuous_subtype_val.comp hcc))
  have hper (h : H) : f (h.val * (y * ofInfinite F G (c 1))) - f (h.val * (y * ofInfinite F G (c 0))) =
      ∫ t in (0 : ℝ)..1, ∑ l : Fin e, (Vel t l : ℂ) * f' l (h.val * (y * ofInfinite F G (c t))) := by
    have hmem : h.val * y ∈ normOneSubgroup F G :=
      (normOneSubgroup F G).mul_mem (unipotent_adelicPoints_mem_normOne j hconn hu h) hy
    simpa only [mul_assoc] using hder (h.val * y) hmem c Vel hc hV hVc
  let Gf (h : H) (t : ℝ) : ℂ :=
    ∑ l : Fin e, (Vel t l : ℂ) * f' l (h.val * (y * ofInfinite F G (c t)))
  have hGc : Continuous (Function.uncurry Gf) := by
    refine continuous_finsetSum _ fun l _ => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply l).comp (hVc.comp continuous_snd))).mul
      ((hf' l).comp ((continuous_subtype_val.comp continuous_fst).mul (hpath.comp continuous_snd)))
  have hint2 : Integrable (Function.uncurry Gf) (ν.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    obtain ⟨M, hM⟩ := (hC.prod isCompact_Icc).exists_bound_of_continuousOn
      (s := C ×ˢ Icc (0 : ℝ) 1) hGc.continuousOn
    refine Integrable.of_bound hGc.aestronglyMeasurable M ?_
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hGc.norm.measurable measurable_const)]
    filter_upwards [hT] with h hh
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hM (h, t) ⟨hh, Ioc_subset_Icc_self ht⟩
  have hfc (z : A) : Continuous fun h : H => f (h.val * z) :=
    hf.comp (continuous_subtype_val.mul continuous_const)
  rw [hrep f hf hfR, hrep f hf hfR,
    ← integral_sub (integrable_of_continuous_of_ae_mem hC hT (hfc _))
      (integrable_of_continuous_of_ae_mem hC hT (hfc _))]
  simp_rw [hper]
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_integral_swap hint2]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  change ∫ h, ∑ l : Fin e, (Vel t l : ℂ) * f' l (h.val * (y * ofInfinite F G (c t))) ∂ν = _
  rw [integral_finsetSum _ (fun l _ => ?_)]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, hrep (f' l) (hf' l) (hf'R l)]
  · exact (integrable_of_continuous_of_ae_mem hC hT
      ((hf' l).comp (continuous_subtype_val.mul continuous_const))).const_mul _

/-- **Joint measurability of constant terms of a family.** -/
theorem measurable_subgroupConstantTerm_family [Smooth U.X.hom]
    (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U) {Ω : Type w} [MeasurableSpace Ω]
    {f : Ω → A → ℂ} (hf : ∀ o, Continuous (f o)) (hfm : Measurable (fun p : Ω × A => f p.1 p.2))
    (hfR : ∀ o (q : RationalGroupPoints F U) x, f o (m (rational F U q) * x) = f o x) :
    Measurable (fun p : Ω × A => subgroupConstantTerm F j (f p.1) p.2) := by
  obtain ⟨ν, C, hν, hC, hνC, hrep⟩ := exists_unipotentFundamentalMeasure j hconn hu
  have heq : (fun p : Ω × A => subgroupConstantTerm F j (f p.1) p.2) =
      fun p => ∫ h, f p.1 (h.val * p.2) ∂ν := by
    funext p
    exact hrep (f p.1) (hf p.1) (hfR p.1) p.2
  rw [heq]
  have hm : Measurable (Function.uncurry fun (p : Ω × A) (h : H) => f p.1 (h.val * p.2)) := by
    have hmul : Measurable fun q : (Ω × A) × H => q.2.val * q.1.2 :=
      (measurable_subtype_coe.comp measurable_snd).mul (measurable_snd.comp measurable_fst)
    exact hfm.comp ((measurable_fst.comp measurable_fst).prodMk hmul)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

end Langlands.Global
