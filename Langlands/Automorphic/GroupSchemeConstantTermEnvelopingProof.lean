import Langlands.Automorphic.GroupSchemeConstantTermEnvelopingStatement
import Langlands.Automorphic.GroupSchemeFiniteVectorDifferential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-! # Enveloping derivatives preserve vanishing parabolic constant terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter Set MeasureTheory
open scoped Classical CategoryTheory.MonObj ContDiff Manifold TensorProduct Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
open Langlands.Geometry.Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

private theorem continuous_constantTermIntegrand_prod (U : GroupScheme.SubgroupFunctor G)
    (f : ContinuousRationalFunctions F G) :
    Continuous (fun p : AdelicGroupPoints F G × AdelicSubgroupPoints.RationalQuotient F G U =>
      constantTermIntegrand F G U f p.1 p.2) := by
  rw [← (IsOpenQuotientMap.id.prodMap
    (LeftCosetSpace.isOpenQuotientMap_mk (AdelicSubgroupPoints.rationalSubgroup F G U))).continuous_comp_iff]
  change Continuous (fun p : AdelicGroupPoints F G × AdelicSubgroupPoints.adelicPoints F G U =>
    evaluate F G f ((p.2 : AdelicGroupPoints F G) * p.1))
  exact f.property.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The derivative along an integral curve of the invariant field is the actual directional
operator evaluated at the translated argument. -/
private theorem hasDerivAt_evaluate_mul :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    ∀ (X : smoothModel F d) (f : FinitePlotSmoothRationalFunctions F G)
      (x : AdelicGroupPoints F G) {curve : ℝ → InfiniteAdelicGroupPoints F G} {t : ℝ},
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) curve t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField X (curve t))) →
      HasDerivAt (fun r => evaluate F G f.val (x * AdelicGroupPoints.ofInfinite F G (curve r)))
        (evaluate F G (finitePlotSmoothDifferentialAction F G hsmooth X f).val
          (x * AdelicGroupPoints.ofInfinite F G (curve t))) t := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  dsimp only
  intro X f x curve t hcurve
  let a := AdelicGroupPoints.infinite F G x
  let b := AdelicGroupPoints.finite F G x
  have hpair (h : InfiniteAdelicGroupPoints F G) :
      x * AdelicGroupPoints.ofInfinite F G h = AdelicGroupPoints.pair F G (a * h) b := by
    rw [AdelicGroupPoints.ofInfinite_eq_pair, ← AdelicGroupPoints.pair_projections F G x,
      AdelicGroupPoints.pair_mul, mul_one]
  let slice := finitePlotSmoothSlice F G b f
  have hs := (isPlotSmooth_iff_contMDiff F G hsmooth _).mp slice.property
  have horbit : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun h => slice.val (a * h)) :=
    hs.comp (contMDiff_const.mul contMDiff_id)
  have hd := ((horbit.mdifferentiableAt (by simp)).hasMFDerivAt.comp t hcurve).hasFDerivAt.hasDerivAt
  have hd' : HasDerivAt (fun r => slice.val (a * curve r))
      (mvfderiv 𝓘(ℝ, smoothModel F d) (fun h => slice.val (a * h)) (curve t)
        (mulInvariantVectorField X (curve t))) t := by
    change HasDerivAt (fun r => slice.val (a * curve r))
      (mvfderiv 𝓘(ℝ, smoothModel F d) (fun h => slice.val (a * h)) (curve t)
        (((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField X (curve t))) 1)) t at hd
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hd
  simp_rw [hpair]
  rw [evaluate_finitePlotSmoothDifferentialAction]
  rw [← groupDirectionalValue_eq_invariant _ X horbit, groupDirectionalValue_leftTranslation] at hd'
  exact hd'

/-- A real directional derivative preserves the kernel of the constant-term integral on a
compact radical quotient. -/
private theorem constantTerm_differential_eq_zero (U : GroupScheme.SubgroupFunctor G)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    [MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    [BorelSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    (mu : Measure (AdelicSubgroupPoints.RationalQuotient F G U)) [IsFiniteMeasure mu]
    (X : smoothModel F d) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : ∀ g, constantTerm F G U mu f.val g = 0) (g : AdelicGroupPoints F G) :
    constantTerm F G U mu (finitePlotSmoothDifferentialAction F G hsmooth X f).val g = 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let model := 𝓘(ℝ, smoothModel F d)
  let : IsManifold model ∞ (InfiniteAdelicGroupPoints F G) := smoothIsManifold F G hsmooth
  let : LieGroup model (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  let v : (x : InfiniteAdelicGroupPoints F G) → TangentSpace model x := mulInvariantVectorField X
  have hv : ContMDiff model model.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle model _)) :=
    (contMDiff_mulInvariantVectorField X).of_le (by simp)
  obtain ⟨curve, hcurve_zero, hintegral_curve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 (x₀ := 1) hv.contMDiffAt
  obtain ⟨ε, hε, hcurve⟩ := Metric.eventually_nhds_iff_ball.mp hintegral_curve
  have hc : ContinuousOn curve (Metric.closedBall 0 (ε / 2)) := fun t ht =>
    (hcurve _ (Metric.closedBall_subset_ball (half_lt_self hε) ht)).continuousAt.continuousWithinAt
  let z (t : ℝ) := g * AdelicGroupPoints.ofInfinite F G (curve t)
  let Df := (finitePlotSmoothDifferentialAction F G hsmooth X f).val
  let Φ (t : ℝ) := constantTermIntegrand F G U f.val (z t)
  let Ψ (t : ℝ) := constantTermIntegrand F G U Df (z t)
  have hz : ContinuousOn z (Metric.closedBall 0 (ε / 2)) :=
    continuous_const.continuousOn.mul
      ((AdelicGroupPoints.ofInfinite F G).continuous.comp_continuousOn hc)
  let rect : Set (ℝ × AdelicSubgroupPoints.RationalQuotient F G U) :=
    Metric.closedBall 0 (ε / 2) ×ˢ univ
  have hrect : IsCompact rect := (isCompact_closedBall (0 : ℝ) (ε / 2)).prod isCompact_univ
  have hfst : ContinuousOn (fun p => z p.1) rect :=
    hz.comp' continuousOn_fst (fun _ hp => hp.1)
  have hpair : ContinuousOn (fun p => (z p.1, p.2)) rect := hfst.prodMk continuousOn_snd
  have hΨ : ContinuousOn (fun p => Ψ p.1 p.2) rect := by
    dsimp only [Ψ]
    let Q := AdelicSubgroupPoints.RationalQuotient F G U
    let integrand (p : AdelicGroupPoints F G × Q) := constantTermIntegrand F G U Df p.1 p.2
    have hi : Continuous integrand := continuous_constantTermIntegrand_prod F G U Df
    set_option backward.isDefEq.respectTransparency true in
      exact Continuous.comp_continuousOn' (α := ℝ × Q) (β := AdelicGroupPoints F G × Q)
        («γ» := ℂ) (g := integrand) (f := fun p => (z p.1, p.2)) (s := rect) hi hpair
  obtain ⟨C, hC⟩ := hrect.exists_bound_of_continuousOn hΨ
  have hdiff : ∀ᵐ q ∂mu, ∀ t ∈ Metric.ball 0 (ε / 2),
      HasDerivAt (fun r => Φ r q) (Ψ t q) t := by
    refine ae_of_all _ fun q t ht => ?_
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective
      (AdelicSubgroupPoints.rationalSubgroup F G U) q
    simpa only [Φ, Ψ, z, constantTermIntegrand_mk, ← mul_assoc] using
      hasDerivAt_evaluate_mul F G hsmooth X f ((n : AdelicGroupPoints F G) * g)
        (hcurve t (Metric.ball_subset_ball (half_le_self hε.le) ht))
  have hint := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Φ) (F' := Ψ) (bound := fun _ => C)
    (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
    (Eventually.of_forall fun t =>
      (continuous_constantTermIntegrand F G U f.val (z t)).aestronglyMeasurable)
    (hasConvergentConstantTerm_of_compact F G U mu f.val (z 0))
    ((continuous_constantTermIntegrand F G U Df (z 0)).aestronglyMeasurable)
    (ae_of_all _ fun q t ht => hC (t, q) ⟨Metric.ball_subset_closedBall ht, mem_univ _⟩)
    (integrable_const C) hdiff).2
  have hzero : (fun t => ∫ q, Φ t q ∂mu) = fun _ => 0 := funext fun t => hf (z t)
  rw [hzero] at hint
  have h := hint.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  change constantTerm F G U mu Df (z 0) = 0 at h
  simpa only [z, hcurve_zero, map_one, mul_one] using h

/-- The actual enveloping action preserves the vanishing space for a compact quotient. -/
private theorem constantTerm_enveloping_eq_zero (U : GroupScheme.SubgroupFunctor G)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    [MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    [BorelSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    (mu : Measure (AdelicSubgroupPoints.RationalQuotient F G U)) [IsFiniteMeasure mu]
    (a : AdelicEnvelopingAlgebra F G hsmooth) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : ∀ g, constantTerm F G U mu f.val g = 0) :
    ∀ g, constantTerm F G U mu (actualAdelicEnvelopingAction F G hsmooth a f).val g = 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let L := (compactConstantTermLinearMap F G U mu).comp
    (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype
  let K := L.ker
  have mem_K (h : FinitePlotSmoothRationalFunctions F G) :
      h ∈ K ↔ ∀ g, constantTerm F G U mu h.val g = 0 := by
    change L h = 0 ↔ _
    exact ⟨fun hh g => congrFun hh g, fun hh => funext hh⟩
  have hcomplex (Z : ℂ ⊗[ℝ] smoothModel F d) (h : FinitePlotSmoothRationalFunctions F G)
      (hh : h ∈ K) : actualAdelicComplexDifferential F G hsmooth Z h ∈ K := by
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      rw [actualAdelicComplexDifferential_tmul, LinearMap.smul_apply]
      exact K.smul_mem c ((mem_K _).mpr
        (constantTerm_differential_eq_zero F G hsmooth U mu X h ((mem_K h).mp hh)))
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply]
      exact K.add_mem hX hY
  have haction (a : AdelicEnvelopingAlgebra F G hsmooth) {h : FinitePlotSmoothRationalFunctions F G}
      (hh : h ∈ K) : actualAdelicEnvelopingAction F G hsmooth a h ∈ K := by
    obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
      (UniversalEnvelopingAlgebra.ringCon ℂ
        (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) a
    change actualAdelicEnvelopingAction F G hsmooth
      (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) h ∈ K
    induction t using TensorAlgebra.induction generalizing h with
    | algebraMap c =>
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
        LinearMap.smul_apply, Module.End.one_apply]
      exact K.smul_mem c hh
    | «ι» Z =>
      change actualAdelicEnvelopingAction F G hsmooth (UniversalEnvelopingAlgebra.ι ℂ Z) h ∈ K
      rw [actualAdelicEnvelopingAction_generator]
      exact hcomplex Z h hh
    | mul x y hx hy =>
      simp only [map_mul, Module.End.mul_apply]
      exact hx (hy hh)
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      exact K.add_mem (hx hh) (hy hh)
  exact (mem_K _).mp (haction a ((mem_K f).mpr hf))

/-- Actual enveloping differentiation preserves vanishing of the normalized constant term. -/
theorem adelicConstantTermEnveloping : AdelicConstantTermEnvelopingStatement.{u} := by
  intro F _ _ G _ _ d hsmooth hPD hG P a f hf
  exact constantTerm_enveloping_eq_zero F G hsmooth (properRationalParabolicRadicals hPD hG P)
    (properParabolicQuotientMeasure F G hPD hG P) a f hf

end Langlands.Automorphic.GroupSchemeFunctions
