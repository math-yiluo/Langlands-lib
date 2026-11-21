import Langlands.Global.AdelicLocalFinitenessCenterStabilityStatement
import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationStatement
import Langlands.Automorphic.GroupSchemeInfiniteTranslation
import Langlands.Automorphic.GroupSchemeConstantTermConsequences
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Langlands.Global.AdelicCompactConstantTermCovariance
import Langlands.Global.AdelicStandardLeviHeightRestriction
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.Automorphic.GroupSchemeUniformGrowthOperators
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison

/-! # Stability of the solutions of `Ξ_main` under the center, from `Ad`-invariance

Bernstein–Lapid, proof of Lemma 8.1: the solution space of `Ξ_main(s)` in `𝔉^R_L` is stable
under the center of the enveloping algebra. This module proves
`LocalFinitenessCenterStabilityStatement` from `AdelicEnvelopingCenterConjugationStatement`
(`Ad(G(F_∞))` fixes the center pointwise). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter Set MeasureTheory
open scoped Classical CategoryTheory.MonObj ContDiff Manifold TensorProduct Topology Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]

/-- The tangent conjugation `g ↦ Ad(g)` of a Lie group is continuous into the continuous linear
endomorphisms of the Lie algebra. -/
theorem continuous_groupTangentConjugation :
    Continuous (fun g : G => groupTangentConjugation 𝓘(ℝ, E) g) := by
  have hman : IsManifold 𝓘(ℝ, E) 1 G := IsManifold.of_le (n := ∞) (by simp)
  rw [continuous_iff_continuousAt]
  intro g₀
  have hf : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (Function.uncurry fun (x h : G) => x * h * x⁻¹) (g₀, (fun _ : G => (1 : G)) g₀) :=
    ((contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv).contMDiffAt
  have h := ContMDiffAt.mfderiv (m := 0) (fun (x h : G) => x * h * x⁻¹) (fun _ : G => (1 : G))
    hf contMDiffAt_const (by simp)
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E) (M := G)) (1 : G)
  have he : (1 : G) ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (1 : G)
  let A : E →L[ℝ] E := e.continuousLinearMapAt ℝ (1 : G)
  let B : E →L[ℝ] E := e.symmL ℝ (1 : G)
  have key : ∀ (c : G → G), c = (fun _ => (1 : G)) →
      ∀ ϕ : (∀ x : G, TangentSpace 𝓘(ℝ, E) (1 : G) →L[ℝ] TangentSpace 𝓘(ℝ, E) (c x)),
        inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ => (1 : G)) c ϕ g₀ =
          fun x => A.comp ((ϕ x : E →L[ℝ] E).comp B) := by
    intro c hc ϕ
    subst hc
    rfl
  have hc : ContinuousAt (fun x : G => A.comp ((groupTangentConjugation 𝓘(ℝ, E) x).comp B))
      g₀ := by
    have h' := h.continuousAt
    rw [key (fun x => x * (1 : G) * x⁻¹) (by funext x; simp)] at h'
    exact h'
  have hBA : ∀ v : E, B (A v) = v := fun v => e.symmL_continuousLinearMapAt he v
  have heq : (fun x : G => groupTangentConjugation 𝓘(ℝ, E) x) =
      fun x => B.comp ((A.comp ((groupTangentConjugation 𝓘(ℝ, E) x).comp B)).comp A) := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    change _ = B (A ((groupTangentConjugation 𝓘(ℝ, E) x) (B (A v))))
    rw [hBA, hBA]
  rw [heq]
  exact (continuous_const.clm_comp continuous_id).continuousAt.comp
    ((hc.clm_comp continuousAt_const))

end Langlands.Geometry.Manifold

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
open Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local instance centerStabilityAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The real tangent conjugation `k ↦ Ad(k)` of `G(F_∞)` is continuous. -/
theorem continuous_adelicTangentConjugation_apply :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ X : smoothModel F d,
      Continuous (fun k : InfiniteAdelicGroupPoints F G => adelicTangentConjugation F G hsmooth k X) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  dsimp only
  intro X
  exact (continuous_groupTangentConjugation (E := smoothModel F d)
    (G := InfiniteAdelicGroupPoints F G)).clm_apply continuous_const

/-- The adjoint orbit `k ↦ Ad(k) a` of every element of the enveloping algebra is a finite sum
of fixed elements with continuous complex coefficients. -/
theorem adelicEnvelopingConjugation_expansion (a : AdelicEnvelopingAlgebra F G hsmooth) :
    ∃ (I : Type) (_ : Fintype I) (c : I → InfiniteAdelicGroupPoints F G → ℂ)
      (e : I → AdelicEnvelopingAlgebra F G hsmooth),
      (∀ i, Continuous (c i)) ∧
        ∀ k, adelicEnvelopingConjugation F G hsmooth k a = ∑ i, c i k • e i := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) a
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    refine ⟨Unit, inferInstance, fun _ _ => z, fun _ => 1, fun _ => continuous_const,
      fun k => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.algebraMap_eq_smul_one,
      map_smul, map_one]
  | «ι» Z =>
    change ∃ (I : Type) (_ : Fintype I) (c : I → InfiniteAdelicGroupPoints F G → ℂ)
      (e : I → AdelicEnvelopingAlgebra F G hsmooth),
      (∀ i, Continuous (c i)) ∧ ∀ k, adelicEnvelopingConjugation F G hsmooth k
        (UniversalEnvelopingAlgebra.ι ℂ Z) = ∑ i, c i k • e i
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      let b := Module.finBasis ℝ (smoothModel F d)
      let b' : Module.Basis (Fin (Module.finrank ℝ (smoothModel F d))) ℝ
        (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) := b
      refine ⟨Fin (Module.finrank ℝ (smoothModel F d)), inferInstance,
        fun j k => ((b.coord j (adelicTangentConjugation F G hsmooth k X) : ℝ) : ℂ) * z,
        fun j => UniversalEnvelopingAlgebra.ι ℂ
          (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
          ((1 : ℂ) ⊗ₜ[ℝ] b' j),
        fun j => ?_, fun k => ?_⟩
      · exact (Complex.continuous_ofReal.comp ((LinearMap.continuous_of_finiteDimensional
          (b.coord j)).comp (continuous_adelicTangentConjugation_apply F G hsmooth X))).mul
          continuous_const
      · rw [adelicEnvelopingConjugation_ι_tmul]
        conv_lhs => rw [← b'.sum_repr (adelicTangentConjugation F G hsmooth k X)]
        rw [TensorProduct.tmul_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only
        rw [← map_smul (UniversalEnvelopingAlgebra.ι ℂ), TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          Complex.real_smul]
        rfl
    | add X Y hX hY =>
      obtain ⟨ι₁, _, c₁, e₁, hc₁, he₁⟩ := hX
      obtain ⟨ι₂, _, c₂, e₂, hc₂, he₂⟩ := hY
      refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim c₁ c₂, Sum.elim e₁ e₂,
        fun i => ?_, fun k => ?_⟩
      · cases i with
        | inl i => exact hc₁ i
        | inr i => exact hc₂ i
      · rw [map_add, map_add, he₁, he₂, Fintype.sum_sum_type]
        rfl
  | mul x y hx hy =>
    obtain ⟨ι₁, _, c₁, e₁, hc₁, he₁⟩ := hx
    obtain ⟨ι₂, _, c₂, e₂, hc₂, he₂⟩ := hy
    refine ⟨ι₁ × ι₂, inferInstance, fun p k => c₁ p.1 k * c₂ p.2 k, fun p => e₁ p.1 * e₂ p.2,
      fun p => (hc₁ p.1).mul (hc₂ p.2), fun k => ?_⟩
    rw [map_mul, map_mul, he₁, he₂, Finset.sum_mul_sum]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  | add x y hx hy =>
    obtain ⟨ι₁, _, c₁, e₁, hc₁, he₁⟩ := hx
    obtain ⟨ι₂, _, c₂, e₂, hc₂, he₂⟩ := hy
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim c₁ c₂, Sum.elim e₁ e₂,
      fun i => ?_, fun k => ?_⟩
    · cases i with
      | inl i => exact hc₁ i
      | inr i => exact hc₂ i
    · rw [map_add, map_add, he₁, he₂, Fintype.sum_sum_type]
      rfl


/-- The derivative along an integral curve of the invariant field is the actual directional
operator evaluated at the translated argument (copied from the private lemma of
`Langlands.Automorphic.GroupSchemeConstantTermEnvelopingProof`). -/
theorem hasDerivAt_evaluate_mul_curve :
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

/-- For every real direction `X` there is a curve `c` in `G(F_∞)` with `c(0) = 1`, continuous
on a closed ball, along which every finite plot-smooth function `f` satisfies
`d/dt f(x c(t)) = (X f)(x c(t))`. -/
theorem exists_differentialCurve :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ X : smoothModel F d, ∃ (curve : ℝ → InfiniteAdelicGroupPoints F G) (ε : ℝ), 0 < ε ∧
      curve 0 = 1 ∧ ContinuousOn curve (Metric.closedBall 0 ε) ∧
      ∀ (f : FinitePlotSmoothRationalFunctions F G) (x : AdelicGroupPoints F G),
        ∀ t ∈ Metric.ball (0 : ℝ) ε,
          HasDerivAt
            (fun r => evaluate F G f.val (x * AdelicGroupPoints.ofInfinite F G (curve r)))
            (evaluate F G (finitePlotSmoothDifferentialAction F G hsmooth X f).val
              (x * AdelicGroupPoints.ofInfinite F G (curve t))) t := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let model := 𝓘(ℝ, smoothModel F d)
  let : IsManifold model ∞ (InfiniteAdelicGroupPoints F G) := smoothIsManifold F G hsmooth
  let : LieGroup model (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  dsimp only
  intro X
  let v : (x : InfiniteAdelicGroupPoints F G) → TangentSpace model x := mulInvariantVectorField X
  have hv : ContMDiff model model.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle model _)) :=
    (contMDiff_mulInvariantVectorField X).of_le (by simp)
  obtain ⟨curve, hcurve_zero, hintegral_curve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 (x₀ := 1) hv.contMDiffAt
  obtain ⟨ε, hε, hcurve⟩ := Metric.eventually_nhds_iff_ball.mp hintegral_curve
  refine ⟨curve, ε / 2, half_pos hε, hcurve_zero, fun t ht => ?_, fun f x t ht => ?_⟩
  · exact (hcurve _ (Metric.closedBall_subset_ball (half_lt_self hε) ht)).continuousAt
      |>.continuousWithinAt
  · exact hasDerivAt_evaluate_mul_curve F G hsmooth X f x
      (hcurve t (Metric.ball_subset_ball (half_le_self hε.le) ht))

/-- A submodule of finite plot-smooth functions that is stable under every real directional
derivative is stable under the whole actual enveloping action. -/
theorem actualAdelicEnvelopingAction_mem_of_differential :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ (K : Submodule ℂ (FinitePlotSmoothRationalFunctions F G)),
      (∀ (X : smoothModel F d) (f : FinitePlotSmoothRationalFunctions F G), f ∈ K →
        finitePlotSmoothDifferentialAction F G hsmooth X f ∈ K) →
      ∀ (a : AdelicEnvelopingAlgebra F G hsmooth) (f : FinitePlotSmoothRationalFunctions F G),
        f ∈ K → actualAdelicEnvelopingAction F G hsmooth a f ∈ K := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  dsimp only
  intro K hK a f hf
  have hcomplex (Z : ℂ ⊗[ℝ] smoothModel F d) (h : FinitePlotSmoothRationalFunctions F G)
      (hh : h ∈ K) : actualAdelicComplexDifferential F G hsmooth Z h ∈ K := by
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      rw [actualAdelicComplexDifferential_tmul, LinearMap.smul_apply]
      exact K.smul_mem c (hK X h hh)
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply]
      exact K.add_mem hX hY
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) a
  change actualAdelicEnvelopingAction F G hsmooth
    (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) f ∈ K
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap c =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
    exact K.smul_mem c hf
  | «ι» Z =>
    change actualAdelicEnvelopingAction F G hsmooth (UniversalEnvelopingAlgebra.ι ℂ Z) f ∈ K
    rw [actualAdelicEnvelopingAction_generator]
    exact hcomplex Z f hf
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply]
    exact hx _ (hy _ hf)
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    exact K.add_mem (hx _ hf) (hy _ hf)

/-- The functions satisfying a left-translation difference equation `D(a) φ = 0` form a
complex subspace. -/
def translationPolynomialSubmodule (a : AdelicGroupPoints F G) (D : Polynomial ℂ) :
    Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {φ | AdelicGroupPoints.IsTranslationPolynomialSolution a D φ}
  add_mem' {φ ψ} hφ hψ g := by
    change ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * (φ (a ^ k * g) + ψ (a ^ k * g)) = 0
    simp only [mul_add, Finset.sum_add_distrib, hφ g, hψ g, add_zero]
  zero_mem' g := by
    change ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * 0 = 0
    simp only [mul_zero, Finset.sum_const_zero]
  smul_mem' c φ hφ g := by
    change ∑ k ∈ Finset.range (D.natDegree + 1), D.coeff k * (c * φ (a ^ k * g)) = 0
    simp_rw [mul_left_comm (D.coeff _) c, ← Finset.mul_sum, hφ g, mul_zero]

/-- A linear map `Λ` from finite plot-smooth functions to functions on `G(𝔸)` that intertwines
real derivatives along curves through `1` carries the actual enveloping action into
solutions of every left-translation difference equation satisfied by `Λ f`. -/
theorem isTranslationPolynomialSolution_enveloping_of_hasDerivAt :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ (Λ : FinitePlotSmoothRationalFunctions F G →ₗ[ℂ] (AdelicGroupPoints F G → ℂ)),
      (∀ (X : smoothModel F d) (f : FinitePlotSmoothRationalFunctions F G),
        ∃ curve : ℝ → InfiniteAdelicGroupPoints F G, curve 0 = 1 ∧
          ∀ x : AdelicGroupPoints F G,
            HasDerivAt (fun t => Λ f (x * AdelicGroupPoints.ofInfinite F G (curve t)))
              (Λ (finitePlotSmoothDifferentialAction F G hsmooth X f) x) 0) →
      ∀ (a : AdelicGroupPoints F G) (D : Polynomial ℂ) (b : AdelicEnvelopingAlgebra F G hsmooth)
        (f : FinitePlotSmoothRationalFunctions F G),
        AdelicGroupPoints.IsTranslationPolynomialSolution a D (Λ f) →
        AdelicGroupPoints.IsTranslationPolynomialSolution a D
          (Λ (actualAdelicEnvelopingAction F G hsmooth b f)) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  dsimp only
  intro Λ hΛ a D b f hf
  let K := (translationPolynomialSubmodule F G a D).comap Λ
  refine actualAdelicEnvelopingAction_mem_of_differential F G hsmooth K
    (fun X h hh g => ?_) b f hf
  obtain ⟨curve, h0, hd⟩ := hΛ X h
  have hzero : (fun t => ∑ k ∈ Finset.range (D.natDegree + 1),
      D.coeff k * Λ h (a ^ k * g * AdelicGroupPoints.ofInfinite F G (curve t))) = fun _ => 0 := by
    funext t
    simp_rw [mul_assoc]
    exact hh (g * AdelicGroupPoints.ofInfinite F G (curve t))
  have hder := HasDerivAt.sum (u := Finset.range (D.natDegree + 1))
    (fun k _ => (hd (a ^ k * g)).const_mul (D.coeff k))
  have hder' : HasDerivAt (fun t => ∑ k ∈ Finset.range (D.natDegree + 1),
      D.coeff k * Λ h (a ^ k * g * AdelicGroupPoints.ofInfinite F G (curve t)))
      (∑ k ∈ Finset.range (D.natDegree + 1),
        D.coeff k * Λ (finitePlotSmoothDifferentialAction F G hsmooth X h) (a ^ k * g)) 0 := by
    convert hder using 1
    funext t
    simp only [Finset.sum_apply]
  rw [hzero] at hder'
  exact hder'.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

/-- Every enveloping derivative of a solution of a left-translation difference equation is again
a solution. -/
theorem isTranslationPolynomialSolution_actualAdelicEnvelopingAction
    (a : AdelicGroupPoints F G) (D : Polynomial ℂ) (b : AdelicEnvelopingAlgebra F G hsmooth)
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : AdelicGroupPoints.IsTranslationPolynomialSolution a D (evaluate F G f.val)) :
    AdelicGroupPoints.IsTranslationPolynomialSolution a D
      (evaluate F G (actualAdelicEnvelopingAction F G hsmooth b f).val) := by
  refine isTranslationPolynomialSolution_enveloping_of_hasDerivAt F G hsmooth
    (finitePlotSmoothEvaluation F G) (fun X h => ?_) a D b f hf
  obtain ⟨curve, ε, hε, h0, -, hd⟩ := exists_differentialCurve F G hsmooth X
  refine ⟨curve, h0, fun x => ?_⟩
  have := hd h x 0 (Metric.mem_ball_self hε)
  change HasDerivAt (fun t => evaluate F G h.val (x * AdelicGroupPoints.ofInfinite F G (curve t)))
    (evaluate F G (finitePlotSmoothDifferentialAction F G hsmooth X h).val x) 0
  simpa only [h0, map_one, mul_one] using this

/-- The constant-term integrand is jointly continuous in the ambient argument and the quotient
point (copied from the private lemma of
`Langlands.Automorphic.GroupSchemeConstantTermEnvelopingProof`). -/
theorem continuous_subgroupConstantTermIntegrand_uncurry (U : GroupScheme.SubgroupFunctor G)
    (f : ContinuousRationalFunctions F G) :
    Continuous (fun p : AdelicGroupPoints F G × AdelicSubgroupPoints.RationalQuotient F G U =>
      constantTermIntegrand F G U f p.1 p.2) := by
  rw [← (IsOpenQuotientMap.id.prodMap
    (LeftCosetSpace.isOpenQuotientMap_mk (AdelicSubgroupPoints.rationalSubgroup F G U))).continuous_comp_iff]
  change Continuous (fun p : AdelicGroupPoints F G × AdelicSubgroupPoints.adelicPoints F G U =>
    evaluate F G f ((p.2 : AdelicGroupPoints F G) * p.1))
  exact f.property.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)

/-- On a compact quotient with a finite measure, the constant term of a finite plot-smooth
function is differentiable along the curve of `exists_differentialCurve`, with derivative the
constant term of the directional derivative. -/
theorem hasDerivAt_constantTerm (U : GroupScheme.SubgroupFunctor G)
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    [MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    [BorelSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
    (mu : Measure (AdelicSubgroupPoints.RationalQuotient F G U)) [IsFiniteMeasure mu] :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ (X : smoothModel F d) (f : FinitePlotSmoothRationalFunctions F G),
      ∃ curve : ℝ → InfiniteAdelicGroupPoints F G, curve 0 = 1 ∧
        ∀ x : AdelicGroupPoints F G,
          HasDerivAt
            (fun t => constantTerm F G U mu f.val (x * AdelicGroupPoints.ofInfinite F G (curve t)))
            (constantTerm F G U mu (finitePlotSmoothDifferentialAction F G hsmooth X f).val x) 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  dsimp only
  intro X f
  obtain ⟨curve, ε, hε, hcurve_zero, hc, hd⟩ := exists_differentialCurve F G hsmooth X
  refine ⟨curve, hcurve_zero, fun g => ?_⟩
  let z (t : ℝ) := g * AdelicGroupPoints.ofInfinite F G (curve t)
  let Df := (finitePlotSmoothDifferentialAction F G hsmooth X f).val
  let Φ (t : ℝ) := constantTermIntegrand F G U f.val (z t)
  let Ψ (t : ℝ) := constantTermIntegrand F G U Df (z t)
  have hz : ContinuousOn z (Metric.closedBall 0 ε) :=
    continuous_const.continuousOn.mul
      ((AdelicGroupPoints.ofInfinite F G).continuous.comp_continuousOn hc)
  let rect : Set (ℝ × AdelicSubgroupPoints.RationalQuotient F G U) :=
    Metric.closedBall 0 ε ×ˢ univ
  have hrect : IsCompact rect := (isCompact_closedBall (0 : ℝ) ε).prod isCompact_univ
  have hfst : ContinuousOn (fun p => z p.1) rect :=
    hz.comp' continuousOn_fst (fun _ hp => hp.1)
  have hpair : ContinuousOn (fun p => (z p.1, p.2)) rect := hfst.prodMk continuousOn_snd
  have hΨ : ContinuousOn (fun p => Ψ p.1 p.2) rect := by
    dsimp only [Ψ]
    let Q := AdelicSubgroupPoints.RationalQuotient F G U
    let integrand (p : AdelicGroupPoints F G × Q) := constantTermIntegrand F G U Df p.1 p.2
    have hi : Continuous integrand := continuous_subgroupConstantTermIntegrand_uncurry F G U Df
    set_option backward.isDefEq.respectTransparency true in
      exact Continuous.comp_continuousOn' (α := ℝ × Q) (β := AdelicGroupPoints F G × Q)
        («γ» := ℂ) (g := integrand) (f := fun p => (z p.1, p.2)) (s := rect) hi hpair
  obtain ⟨C, hC⟩ := hrect.exists_bound_of_continuousOn hΨ
  have hdiff : ∀ᵐ q ∂mu, ∀ t ∈ Metric.ball 0 ε,
      HasDerivAt (fun r => Φ r q) (Ψ t q) t := by
    refine ae_of_all _ fun q t ht => ?_
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective
      (AdelicSubgroupPoints.rationalSubgroup F G U) q
    simpa only [Φ, Ψ, z, constantTermIntegrand_mk, ← mul_assoc] using
      hd f ((n : AdelicGroupPoints F G) * g) t ht
  have hint := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Φ) (F' := Ψ) (bound := fun _ => C)
    (Metric.ball_mem_nhds (0 : ℝ) hε)
    (Eventually.of_forall fun t =>
      (continuous_constantTermIntegrand F G U f.val (z t)).aestronglyMeasurable)
    (hasConvergentConstantTerm_of_compact F G U mu f.val (z 0))
    ((continuous_constantTermIntegrand F G U Df (z 0)).aestronglyMeasurable)
    (ae_of_all _ fun q t ht => hC (t, q) ⟨Metric.ball_subset_closedBall ht, mem_univ _⟩)
    (integrable_const C) hdiff).2
  have hz0 : z 0 = g := by simp only [z, hcurve_zero, map_one, mul_one]
  change HasDerivAt (fun t => ∫ q, Φ t q ∂mu) (constantTerm F G U mu Df (z 0)) 0 at hint
  rw [hz0] at hint
  exact hint

/-- On a compact quotient, every enveloping derivative of a function whose constant term
along a represented subgroup solves a left-translation difference equation has the same
property. -/
theorem isTranslationPolynomialSolution_subgroupConstantTerm_enveloping
    [LocallyOfFiniteType G.X.hom] {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]
    (a : AdelicGroupPoints F G) (D : Polynomial ℂ) (b : AdelicEnvelopingAlgebra F G hsmooth)
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : AdelicGroupPoints.IsTranslationPolynomialSolution a D
      (AdelicGroupPoints.subgroupConstantTerm F j (evaluate F G f.val))) :
    AdelicGroupPoints.IsTranslationPolynomialSolution a D
      (AdelicGroupPoints.subgroupConstantTerm F j
        (evaluate F G (actualAdelicEnvelopingAction F G hsmooth b f).val)) := by
  let V := SubgroupFunctor.range j
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : BorelSpace (AdelicSubgroupPoints.RationalQuotient F G V) :=
    AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  let ν := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
  let Λ := (compactConstantTermLinearMap F G V ν).comp
    (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype
  have hΛ (h : FinitePlotSmoothRationalFunctions F G) :
      AdelicGroupPoints.subgroupConstantTerm F j (evaluate F G h.val) = Λ h :=
    funext (AdelicGroupPoints.subgroupConstantTerm_eq_continuousConstantTerm j h.val)
  rw [hΛ] at hf ⊢
  exact isTranslationPolynomialSolution_enveloping_of_hasDerivAt F G hsmooth Λ
    (fun X h => hasDerivAt_constantTerm F G hsmooth V ν X h) a D b f hf

section HarishChandra

/-- Right translation by `g ∈ G(𝔸)` intertwines the enveloping action twisted by the adjoint
action of the infinite component: `a (R(g) f) = R(g) (Ad(g_∞⁻¹) a f)`. -/
theorem actualAdelicEnvelopingAction_finitePlotSmoothRightAction
    (g : AdelicGroupPoints F G) (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : FinitePlotSmoothRationalFunctions F G) :
    actualAdelicEnvelopingAction F G hsmooth a (finitePlotSmoothRightAction F G g f) =
      finitePlotSmoothRightAction F G g (actualAdelicEnvelopingAction F G hsmooth
        (adelicEnvelopingConjugation F G hsmooth (AdelicGroupPoints.infinite F G g)⁻¹ a) f) := by
  have hg : AdelicGroupPoints.ofInfinite F G (AdelicGroupPoints.infinite F G g) *
      AdelicGroupPoints.ofFinite F G (AdelicGroupPoints.finite F G g) = g := by
    rw [AdelicGroupPoints.ofInfinite_eq_pair, AdelicGroupPoints.ofFinite_eq_pair,
      AdelicGroupPoints.pair_mul, mul_one, one_mul, AdelicGroupPoints.pair_projections]
  have hR : finitePlotSmoothRightAction F G g =
      finitePlotSmoothRightAction F G
          (AdelicGroupPoints.ofInfinite F G (AdelicGroupPoints.infinite F G g)) *
        finitePlotSmoothRightAction F G
          (AdelicGroupPoints.ofFinite F G (AdelicGroupPoints.finite F G g)) := by
    rw [← map_mul, hg]
  rw [hR, Module.End.mul_apply, Module.End.mul_apply,
    actualAdelicEnvelopingAction_eq F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth),
    ← finitePlotSmoothEnvelopingAction_finiteRightAction F G hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth)]
  change _ = finitePlotSmoothRightAction F G
    (AdelicGroupPoints.ofInfinite F G (AdelicGroupPoints.infinite F G g))
    (actualAdelicEnvelopingAction F G hsmooth _ _)
  rw [finitePlotSmoothRightAction_actualAdelicEnvelopingAction,
    adelicEnvelopingConjugation_apply_inv]
  rfl

/-- Evaluation of a finite linear combination of finite plot-smooth functions. -/
theorem evaluate_sum_smul {I : Type*} [Fintype I] (c : I → ℂ)
    (h : I → FinitePlotSmoothRationalFunctions F G) (y : AdelicGroupPoints F G) :
    evaluate F G (∑ i, c i • h i).val y = ∑ i, c i * evaluate F G (h i).val y := by
  change finitePlotSmoothEvaluation F G (∑ i, c i • h i) y = _
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

/-- The function `Ψ_a(g, y) = (a R(g) f)(y)` of `g, y ∈ G(𝔸)`, for `a` in the enveloping algebra
and `R` the right translation. -/
def envelopingTranslate (f : FinitePlotSmoothRationalFunctions F G)
    (a : AdelicEnvelopingAlgebra F G hsmooth) (g y : AdelicGroupPoints F G) : ℂ :=
  evaluate F G (actualAdelicEnvelopingAction F G hsmooth a
    (finitePlotSmoothRightAction F G g f)).val y

/-- `Ψ_{a + a'} = Ψ_a + Ψ_{a'}`. -/
theorem envelopingTranslate_add (f : FinitePlotSmoothRationalFunctions F G)
    (a a' : AdelicEnvelopingAlgebra F G hsmooth) (g y : AdelicGroupPoints F G) :
    envelopingTranslate F G hsmooth f (a + a') g y =
      envelopingTranslate F G hsmooth f a g y + envelopingTranslate F G hsmooth f a' g y := by
  unfold envelopingTranslate
  rw [map_add, LinearMap.add_apply]
  rfl

/-- `Ψ_{r a} = r Ψ_a`. -/
theorem envelopingTranslate_smul (f : FinitePlotSmoothRationalFunctions F G) (r : ℂ)
    (a : AdelicEnvelopingAlgebra F G hsmooth) (g y : AdelicGroupPoints F G) :
    envelopingTranslate F G hsmooth f (r • a) g y = r * envelopingTranslate F G hsmooth f a g y := by
  unfold envelopingTranslate
  rw [map_smul, LinearMap.smul_apply]
  rfl

/-- `Ψ_0 = 0`. -/
theorem envelopingTranslate_zero (f : FinitePlotSmoothRationalFunctions F G)
    (g y : AdelicGroupPoints F G) :
    envelopingTranslate F G hsmooth f 0 g y = 0 := by
  unfold envelopingTranslate
  rw [map_zero, LinearMap.zero_apply]
  rfl

/-- `((a + a') f)(y) = (a f)(y) + (a' f)(y)`. -/
theorem evaluate_actualAdelicEnvelopingAction_add (f : FinitePlotSmoothRationalFunctions F G)
    (a a' : AdelicEnvelopingAlgebra F G hsmooth) (y : AdelicGroupPoints F G) :
    evaluate F G (actualAdelicEnvelopingAction F G hsmooth (a + a') f).val y =
      evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val y +
        evaluate F G (actualAdelicEnvelopingAction F G hsmooth a' f).val y := by
  rw [map_add, LinearMap.add_apply]
  rfl

/-- `((r a) f)(y) = r (a f)(y)`. -/
theorem evaluate_actualAdelicEnvelopingAction_smul (f : FinitePlotSmoothRationalFunctions F G)
    (r : ℂ) (a : AdelicEnvelopingAlgebra F G hsmooth) (y : AdelicGroupPoints F G) :
    evaluate F G (actualAdelicEnvelopingAction F G hsmooth (r • a) f).val y =
      r * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val y := by
  rw [map_smul, LinearMap.smul_apply]
  rfl

/-- `(0 f)(y) = 0`. -/
theorem evaluate_actualAdelicEnvelopingAction_zero (f : FinitePlotSmoothRationalFunctions F G)
    (y : AdelicGroupPoints F G) :
    evaluate F G (actualAdelicEnvelopingAction F G hsmooth 0 f).val y = 0 := by
  rw [map_zero, LinearMap.zero_apply]
  rfl

/-- `Ψ_a(g, y)` is jointly continuous: by the covariance and the expansion of `Ad(g_∞⁻¹) a`,
it is a finite sum of `c_i(g_∞⁻¹) (e_i f)(y g)` with continuous `c_i`. -/
theorem continuous_envelopingTranslate (f : FinitePlotSmoothRationalFunctions F G)
    (a : AdelicEnvelopingAlgebra F G hsmooth) :
    Continuous (fun p : AdelicGroupPoints F G × AdelicGroupPoints F G =>
      envelopingTranslate F G hsmooth f a p.1 p.2) := by
  obtain ⟨I, _, c, e, hc, he⟩ := adelicEnvelopingConjugation_expansion F G hsmooth a
  have heq : (fun p : AdelicGroupPoints F G × AdelicGroupPoints F G =>
      envelopingTranslate F G hsmooth f a p.1 p.2) =
      fun p => ∑ i, c i (AdelicGroupPoints.infinite F G p.1)⁻¹ *
        evaluate F G (actualAdelicEnvelopingAction F G hsmooth (e i) f).val (p.2 * p.1) := by
    funext p
    unfold envelopingTranslate
    rw [actualAdelicEnvelopingAction_finitePlotSmoothRightAction, he, map_sum,
      LinearMap.sum_apply]
    change evaluate F G (∑ i, actualAdelicEnvelopingAction F G hsmooth
      (c i (AdelicGroupPoints.infinite F G p.1)⁻¹ • e i) f).val (p.2 * p.1) = _
    simp only [map_smul, LinearMap.smul_apply]
    exact evaluate_sum_smul F G _ _ _
  rw [heq]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((hc i).comp ((AdelicGroupPoints.infinite F G).continuous.comp continuous_fst).inv).mul
    ((actualAdelicEnvelopingAction F G hsmooth (e i) f).val.property.comp
      (continuous_snd.mul continuous_fst))

variable [LocallyOfFiniteType G.X.hom]

/-- Differentiation under the integral sign against a continuous compactly supported kernel. -/
theorem hasDerivAt_integral_mul_of_continuous {h : AdelicGroupPoints F G → ℂ}
    (hh : Continuous h) (hhs : HasCompactSupport h)
    {Ψ Ψ' : AdelicGroupPoints F G → AdelicGroupPoints F G → ℂ}
    (hΨ : Continuous fun p : AdelicGroupPoints F G × AdelicGroupPoints F G => Ψ p.1 p.2)
    (hΨ' : Continuous fun p : AdelicGroupPoints F G × AdelicGroupPoints F G => Ψ' p.1 p.2)
    {z : ℝ → AdelicGroupPoints F G} {ε : ℝ} (hε : 0 < ε)
    (hz : ContinuousOn z (Metric.closedBall 0 ε))
    (hd : ∀ g, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun r => Ψ g (z r)) (Ψ' g (z t)) t) :
    HasDerivAt (fun t => ∫ g, h g * Ψ g (z t) ∂(Measure.haar : Measure (AdelicGroupPoints F G)))
      (∫ g, h g * Ψ' g (z 0) ∂(Measure.haar : Measure (AdelicGroupPoints F G))) 0 := by
  let S : Set (ℝ × AdelicGroupPoints F G) := Metric.closedBall (0 : ℝ) ε ×ˢ tsupport h
  have hS : IsCompact S := (isCompact_closedBall 0 ε).prod hhs
  have hcont : ContinuousOn (fun p : ℝ × AdelicGroupPoints F G => Ψ' p.2 (z p.1)) S :=
    hΨ'.comp_continuousOn (continuousOn_snd.prodMk (hz.comp continuousOn_fst fun _ hp => hp.1))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  have hbound : ∀ g, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖h g * Ψ' g (z t)‖ ≤ ‖h g‖ * C := by
    intro g t ht
    by_cases hg : g ∈ tsupport h
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC (t, g) ⟨Metric.ball_subset_closedBall ht, hg⟩)
        (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul, norm_zero, zero_mul]
  have hcontΨ (y : AdelicGroupPoints F G) : Continuous fun g => Ψ g y :=
    hΨ.comp (continuous_id.prodMk continuous_const)
  have hcontΨ' (y : AdelicGroupPoints F G) : Continuous fun g => Ψ' g y :=
    hΨ'.comp (continuous_id.prodMk continuous_const)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t g => h g * Ψ g (z t)) (F' := fun t g => h g * Ψ' g (z t))
    (bound := fun g => ‖h g‖ * C)
    (Metric.ball_mem_nhds (0 : ℝ) hε)
    (Eventually.of_forall fun t => (hh.mul (hcontΨ (z t))).aestronglyMeasurable)
    ((hh.mul (hcontΨ (z 0))).integrable_of_hasCompactSupport hhs.mul_right)
    ((hh.mul (hcontΨ' (z 0))).aestronglyMeasurable)
    (ae_of_all _ fun g t ht => hbound g t ht)
    ((hh.norm.integrable_of_hasCompactSupport hhs.norm).mul_const C)
    (ae_of_all _ fun g t ht => (hd g t ht).const_mul (h g))).2

/-- One step of the Harish-Chandra induction: if `a'` acts as `X ∘ a` for a real direction `X`,
then the convolution identity for `a` implies the one for `a'`. -/
theorem harishChandra_differential_step {K : Type*} [Fintype K] (b : K → ℂ)
    (h : K → AdelicGroupPoints F G → ℂ) (hh : ∀ k, Continuous (h k))
    (hhs : ∀ k, HasCompactSupport (h k)) (c : ℂ) (f : FinitePlotSmoothRationalFunctions F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ (X : smoothModel F d) (a a' : AdelicEnvelopingAlgebra F G hsmooth),
      (∀ φ, actualAdelicEnvelopingAction F G hsmooth a' φ =
        finitePlotSmoothDifferentialAction F G hsmooth X (actualAdelicEnvelopingAction F G hsmooth a φ)) →
      (∀ y, ∑ k, b k * ∫ g, h k g * envelopingTranslate F G hsmooth f a g y
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
        c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val y) →
      ∀ y, ∑ k, b k * ∫ g, h k g * envelopingTranslate F G hsmooth f a' g y
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
        c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a' f).val y := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  dsimp only
  intro X a a' ha' ha x
  obtain ⟨curve, ε, hε, h0, hc, hd⟩ := exists_differentialCurve F G hsmooth X
  let z (t : ℝ) := x * AdelicGroupPoints.ofInfinite F G (curve t)
  have hz : ContinuousOn z (Metric.closedBall 0 ε) :=
    continuous_const.continuousOn.mul
      ((AdelicGroupPoints.ofInfinite F G).continuous.comp_continuousOn hc)
  have hz0 : z 0 = x := by simp only [z, h0, map_one, mul_one]
  have hR : HasDerivAt (fun t => ∑ k, b k * ∫ g, h k g * envelopingTranslate F G hsmooth f a g (z t)
        ∂(Measure.haar : Measure (AdelicGroupPoints F G)))
      (∑ k, b k * ∫ g, h k g * envelopingTranslate F G hsmooth f a' g (z 0)
        ∂(Measure.haar : Measure (AdelicGroupPoints F G))) 0 := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    refine (hasDerivAt_integral_mul_of_continuous F G (hh k) (hhs k)
      (continuous_envelopingTranslate F G hsmooth f a)
      (continuous_envelopingTranslate F G hsmooth f a') hε hz fun g t ht => ?_).const_mul (b k)
    change HasDerivAt (fun r => evaluate F G (actualAdelicEnvelopingAction F G hsmooth a
        (finitePlotSmoothRightAction F G g f)).val (x * AdelicGroupPoints.ofInfinite F G (curve r)))
      (evaluate F G (actualAdelicEnvelopingAction F G hsmooth a'
        (finitePlotSmoothRightAction F G g f)).val (x * AdelicGroupPoints.ofInfinite F G (curve t))) t
    rw [ha']
    exact hd _ x t ht
  have hL : HasDerivAt (fun t => c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val (z t))
      (c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a' f).val (z 0)) 0 := by
    rw [ha']
    exact (hd _ x 0 (Metric.mem_ball_self hε)).const_mul c
  have hfun : (fun t => ∑ k, b k * ∫ g, h k g * envelopingTranslate F G hsmooth f a g (z t)
        ∂(Measure.haar : Measure (AdelicGroupPoints F G))) =
      fun t => c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val (z t) :=
    funext fun t => ha (z t)
  rw [hfun] at hR
  have := hR.unique hL
  rwa [hz0] at this

/-- The convolution identity `∑_k b_k ∫ h_k(g) (a R(g) f)(y) dg = c (a f)(y)` propagates from
`a = 1` (the Harish-Chandra equation of `f`) to every element `a` of the enveloping algebra. -/
theorem harishChandra_actualAdelicEnvelopingAction {K : Type*} [Fintype K] (b : K → ℂ)
    (h : K → AdelicGroupPoints F G → ℂ) (hh : ∀ k, Continuous (h k))
    (hhs : ∀ k, HasCompactSupport (h k)) (c : ℂ) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : ∀ x, ∑ k, b k * AdelicGroupPoints.rightConvolution F G (h k) (evaluate F G f.val) x =
      c * evaluate F G f.val x)
    (a : AdelicEnvelopingAlgebra F G hsmooth) (x : AdelicGroupPoints F G) :
    ∑ k, b k * ∫ g, h k g * envelopingTranslate F G hsmooth f a g x
        ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
      c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val x := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  have hint (a : AdelicEnvelopingAlgebra F G hsmooth) (k : K) (y : AdelicGroupPoints F G) :
      Integrable (fun g => h k g * envelopingTranslate F G hsmooth f a g y)
        (Measure.haar : Measure (AdelicGroupPoints F G)) :=
    ((hh k).mul ((continuous_envelopingTranslate F G hsmooth f a).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport (hhs k).mul_right
  let A : Submodule ℂ (AdelicEnvelopingAlgebra F G hsmooth) :=
    { carrier := {a | ∀ y, ∑ k, b k * ∫ g, h k g * envelopingTranslate F G hsmooth f a g y
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
        c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val y}
      add_mem' := by
        intro a a' ha ha' y
        have e1 (k : K) : ∫ g, h k g * envelopingTranslate F G hsmooth f (a + a') g y
            ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
            (∫ g, h k g * envelopingTranslate F G hsmooth f a g y
              ∂(Measure.haar : Measure (AdelicGroupPoints F G))) +
            ∫ g, h k g * envelopingTranslate F G hsmooth f a' g y
              ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
          rw [← integral_add (hint a k y) (hint a' k y)]
          simp only [envelopingTranslate_add, mul_add]
        simp only [e1, mul_add, Finset.sum_add_distrib, evaluate_actualAdelicEnvelopingAction_add]
        rw [ha y, ha' y]
      zero_mem' := by
        intro y
        simp only [envelopingTranslate_zero, mul_zero, integral_zero, Finset.sum_const_zero,
          evaluate_actualAdelicEnvelopingAction_zero]
      smul_mem' := by
        intro r a ha y
        have e1 (k : K) : ∫ g, h k g * envelopingTranslate F G hsmooth f (r • a) g y
            ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
            r * ∫ g, h k g * envelopingTranslate F G hsmooth f a g y
              ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun g => ?_)
          simp only [envelopingTranslate_smul]
          ring
        simp only [e1, evaluate_actualAdelicEnvelopingAction_smul]
        rw [mul_left_comm c r, ← ha y, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring }
  have hgen : ∀ (X : smoothModel F d) (a : AdelicEnvelopingAlgebra F G hsmooth), a ∈ A →
      UniversalEnvelopingAlgebra.ι ℂ
        (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
        ((1 : ℂ) ⊗ₜ[ℝ] X) * a ∈ A := by
    intro X a ha
    exact harishChandra_differential_step F G hsmooth b h hh hhs c f X a _ (fun φ => by
      rw [map_mul, Module.End.mul_apply, actualAdelicEnvelopingAction_generator,
        actualAdelicComplexDifferential_tmul, LinearMap.smul_apply, one_smul]) ha
  have hmul : ∀ t : TensorAlgebra ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
      ∀ a ∈ A, UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t * a ∈ A := by
    intro t
    induction t using TensorAlgebra.induction with
    | algebraMap r =>
      intro a ha
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact A.smul_mem r ha
    | «ι» Z =>
      intro a ha
      change UniversalEnvelopingAlgebra.ι ℂ Z * a ∈ A
      induction Z using TensorProduct.inductionOn with
      | tmul r X =>
        have hrX : (r ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d)
            (InfiniteAdelicGroupPoints F G)) = r • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hrX, map_smul, smul_mul_assoc]
        exact A.smul_mem r (hgen X a ha)
      | add Z₁ Z₂ h₁ h₂ =>
        rw [map_add, add_mul]
        exact A.add_mem h₁ h₂
    | mul x y hx hy =>
      intro a ha
      rw [map_mul, mul_assoc]
      exact hx _ (hy a ha)
    | add x y hx hy =>
      intro a ha
      rw [map_add, add_mul]
      exact A.add_mem (hx a ha) (hy a ha)
  have h1 : (1 : AdelicEnvelopingAlgebra F G hsmooth) ∈ A := by
    change ∀ y, _
    intro y
    have e (g : AdelicGroupPoints F G) :
        envelopingTranslate F G hsmooth f 1 g y = evaluate F G f.val (y * g) := by
      unfold envelopingTranslate
      rw [map_one, Module.End.one_apply]
      rfl
    simp only [e]
    rw [map_one, Module.End.one_apply]
    exact hf y
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) a
  have := hmul t 1 h1
  rw [mul_one] at this
  exact this x

/-- If `Ad(G(F_∞))` fixes a central element `Y`, then `Y f` satisfies every Harish-Chandra
equation `∑_k b_k δ(h_k) f = c f` satisfied by `f`. -/
theorem rightConvolution_actualAdelicEnvelopingAction_of_conjugation {K : Type*} [Fintype K]
    (b : K → ℂ) (h : K → AdelicGroupPoints F G → ℂ) (hh : ∀ k, Continuous (h k))
    (hhs : ∀ k, HasCompactSupport (h k)) (c : ℂ) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : ∀ x, ∑ k, b k * AdelicGroupPoints.rightConvolution F G (h k) (evaluate F G f.val) x =
      c * evaluate F G f.val x)
    (Y : AdelicEnvelopingAlgebra F G hsmooth)
    (hY : ∀ k : InfiniteAdelicGroupPoints F G, adelicEnvelopingConjugation F G hsmooth k Y = Y)
    (x : AdelicGroupPoints F G) :
    ∑ k, b k * AdelicGroupPoints.rightConvolution F G (h k)
        (evaluate F G (actualAdelicEnvelopingAction F G hsmooth Y f).val) x =
      c * evaluate F G (actualAdelicEnvelopingAction F G hsmooth Y f).val x := by
  have key := harishChandra_actualAdelicEnvelopingAction F G hsmooth b h hh hhs c f hf Y x
  have e (g : AdelicGroupPoints F G) : envelopingTranslate F G hsmooth f Y g x =
      evaluate F G (actualAdelicEnvelopingAction F G hsmooth Y f).val (x * g) := by
    unfold envelopingTranslate
    rw [actualAdelicEnvelopingAction_finitePlotSmoothRightAction, hY]
    rfl
  simp only [e] at key
  exact key

end HarishChandra

end Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme

/-- The actual adelic quotient of a standard unipotent subgroup `U_J` (`J ⊆ Δ₀`) of a connected
reductive group is compact. -/
theorem compactSpace_rationalQuotient_standardUnipotent (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (T : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (iT : T.toGrp ⟶ G) (ν : cocharacterLattice T) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus iT) (hν : IsGenericCocharacter iT ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots iT ν) :
    CompactSpace (RationalQuotient F G (standardUnipotent iT ν J)) := by
  let : Smooth G.X.hom := hG.smooth
  have hcl : IsClosedImmersion (Standard.unipotentHom iT ν J).hom.hom.left :=
    Standard.isClosedSubgroup_unipotentHom iT ν J
  have : IsAffineHom (Standard.unipotentScheme iT ν J).X.hom := by
    rw [← Over.w (Standard.unipotentHom iT ν J).hom.hom]
    infer_instance
  have : IsAffine (Standard.unipotentScheme iT ν J).X.left :=
    isAffine_of_isAffineHom (Standard.unipotentScheme iT ν J).X.hom
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter F G hG T iT hi ν hν J hJ
  have hU := Standard.isRepresentedBy_unipotentHom iT ν J
  have hrange := hU.2
  rw [(heq ζ hζ).2.2] at hU
  have hs := (dynamicSmooth F G _ _ _).2.2 hU
  have hc := (dynamicConnected F G _ _ _).1 hU
  have hu := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T iT ν hG hi hν J hJ
  have := compactSpace_rationalQuotient_range_unipotent F (Standard.unipotentHom iT ν J) hs hc hu
  rwa [hrange] at this

end Langlands.Global.AdelicSubgroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- `𝔷`-stability of the solutions of `Ξ_main` (Bernstein–Lapid, proof of Lemma 8.1) follows from
the invariance of the center of the enveloping algebra under `Ad(G(F_∞))`. -/
theorem localFinitenessCenterStability_of
    (hAd : AdelicEnvelopingCenterConjugationStatement.{u}) :
    LocalFinitenessCenterStabilityStatement.{u} := by
  intro F _ _ G T _ _ _ iT ν hG hi hν Ua _ u _ t r z hdata N d rho hN hrho hsmooth hcalc n W X hX
    L hLo hLc R s v hv Y
  let f : FinitePlotSmoothRationalFunctions F G :=
    (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val
  refine ⟨UniformGrowthFrechetSpace.envelopingActionCLM F G rho hsmooth hcalc hN hrho R L Y.val v,
    ⟨?_, ?_, ?_⟩, rfl⟩
  · intro i x
    exact rightConvolution_actualAdelicEnvelopingAction_of_conjugation F G hsmooth
      (fun k => X.b i k s) (X.h i) (fun k => (hX.1 i k).1.1) (fun k => (hX.1 i k).2.1)
      (X.c i s) f (hv.1 i) Y.val (fun k => hAd F G hsmooth hG k Y.val Y.property) x
  · intro α
    have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (u α))) := by
      rw [hdata.1 α]
      exact AdelicSubgroupPoints.compactSpace_rationalQuotient_standardUnipotent F G T iT ν hG hi hν
        _ Set.sdiff_subset
    exact isTranslationPolynomialSolution_subgroupConstantTerm_enveloping F G hsmooth (u α) _ _
      Y.val f (hv.2.1 α)
  · intro j
    exact isTranslationPolynomialSolution_actualAdelicEnvelopingAction F G hsmooth _ _ Y.val f
      (hv.2.2 j)

end Langlands.Global
