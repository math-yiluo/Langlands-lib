import Langlands.Analysis.Local.CompactFactorizationHaar
import Langlands.Global.AdelicTestConvolution

/-! # Compact averaging of adelic test kernels -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj ContDiff Manifold Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure A)

variable {K : Subgroup (InfiniteAdelicGroupPoints F G)} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (measure : Measure K) [IsFiniteMeasure measure]

variable (F G) in
private def compactInclusion (K : Subgroup A∞) : K →* A :=
  (ofInfinite F G).toMonoidHom.comp K.subtype

local notation "j" => compactInclusion F G K

omit [LocallyOfFiniteType G.X.hom] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
private theorem continuous_compactInclusion : Continuous (j : K → A) :=
  (ofInfinite F G).continuous.comp continuous_subtype_val

/-- Average left translates of a kernel with a continuous weight on the compact group. -/
def leftCompactKernelAverage (weight : C(K, ℂ)) (h : A → ℂ) (x : A) : ℂ :=
  ∫ k, weight k * h ((j k)⁻¹ * x) ∂measure

/-- Average the translates `x ↦ h(xk)` with a continuous weight on the compact group. -/
def rightCompactKernelAverage (weight : C(K, ℂ)) (h : A → ℂ) (x : A) : ℂ :=
  ∫ k, weight k * h (x * j k) ∂measure

omit [LocallyOfFiniteType G.X.hom] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure measure] in
theorem rightCompactKernelAverage_eq (weight : C(K, ℂ)) (h : A → ℂ) :
    rightCompactKernelAverage measure weight h =
      fun x => leftCompactKernelAverage measure weight (fun y => h y⁻¹) x⁻¹ := by
  funext x
  simp only [rightCompactKernelAverage, leftCompactKernelAverage, mul_inv_rev, inv_inv]

theorem isAdelicTestFunction_leftCompactKernelAverage {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (weight : C(K, ℂ)) {h : A → ℂ} (hh : IsAdelicTestFunction F G h) :
    IsAdelicTestFunction F G (leftCompactKernelAverage measure weight h) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothIsManifold F G hsmooth
  let := smoothLieGroup F G hsmooth
  obtain ⟨L, hLo, hL⟩ := hh.1.2.2
  obtain ⟨R, hRo, hR⟩ := hh.2.2
  refine ⟨⟨?_, ?_, L, hLo, ?_⟩, ?_, R, hRo, ?_⟩
  · have hcont : Continuous (fun y : A × K => weight y.2 * h ((j y.2)⁻¹ * y.1)) :=
      (weight.continuous.comp continuous_snd).mul
        (hh.1.1.comp ((continuous_compactInclusion.comp continuous_snd).inv.mul continuous_fst))
    change Continuous (fun x : A => ∫ k, weight k * h ((j k)⁻¹ * x) ∂measure)
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous hcont (s := Set.univ) isCompact_univ
  · intro b
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).2
    let I := 𝓘(ℝ, smoothModel F d)
    let inc : C(K, A∞) := ⟨Subtype.val, continuous_subtype_val⟩
    let H (y : A∞ × A∞) := h (pair F G (y.2⁻¹ * y.1) b)
    have hH : ContMDiff (I.prod I) 𝓘(ℝ, ℂ) ∞ H :=
      ((isPlotSmooth_iff_contMDiff F G hsmooth _).1 (hh.1.2.1 b)).comp
        (contMDiff_snd.inv.mul contMDiff_fst)
    apply (Langlands.Analysis.CompactManifoldVectorIntegral.contMDiff_weightedIntegral
      measure weight inc hH).congr
    intro a
    unfold functionInfiniteSlice leftCompactKernelAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun k => by
      change weight k * h ((ofInfinite F G k.val)⁻¹ * pair F G a b) =
        weight k * h (pair F G (k.val⁻¹ * a) b)
      rw [← map_inv (ofInfinite F G) k.val, ofInfinite_eq_pair, pair_mul, one_mul]
  · intro k hk x
    unfold leftCompactKernelAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      change weight a * h ((j a)⁻¹ * (x * ofFinite F G k)) = weight a * h ((j a)⁻¹ * x)
      rw [← mul_assoc, hL k hk]
  · exact HasCompactSupport.of_support_subset_isCompact
      ((isCompact_range continuous_compactInclusion).mul hh.2.1.isCompact) (by
        intro x hx
        by_contra hn
        apply hx
        apply integral_eq_zero_of_ae
        apply Filter.Eventually.of_forall
        intro k
        have hnot : (j k)⁻¹ * x ∉ tsupport h := by
          intro hm
          exact hn ⟨j k, ⟨k, rfl⟩, _, hm, by simp⟩
        change weight k * h ((j k)⁻¹ * x) = 0
        rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero])
  · intro k hk x
    have hcomm (a : K) : Commute (j a) (ofFinite F G k) :=
      factors_commute F G a.val k
    unfold leftCompactKernelAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by
      change weight a * h ((j a)⁻¹ * (ofFinite F G k * x)) = weight a * h ((j a)⁻¹ * x)
      rw [← mul_assoc, (hcomm a).inv_left.eq, mul_assoc, hR k hk]

theorem isAdelicTestFunction_rightCompactKernelAverage {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (weight : C(K, ℂ)) {h : A → ℂ} (hh : IsAdelicTestFunction F G h) :
    IsAdelicTestFunction F G (rightCompactKernelAverage measure weight h) := by
  rw [rightCompactKernelAverage_eq]
  exact isAdelicTestFunction_comp_inv hsmooth
    (isAdelicTestFunction_leftCompactKernelAverage measure hsmooth weight
      (isAdelicTestFunction_comp_inv hsmooth hh))

private theorem finiteDimensional_span_continuousMap {X Y : Type*} [TopologicalSpace Y]
    (f : X → C(Y, ℂ))
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x => (f x : Y → ℂ)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := by
  let L : C(Y, ℂ) →ₗ[ℂ] (Y → ℂ) := ContinuousMap.coeFnLinearMap ℂ
  let e := Submodule.equivMapOfInjective L ContinuousMap.coe_injective
    (Submodule.span ℂ (Set.range f))
  have he : (Submodule.span ℂ (Set.range f)).map L =
      Submodule.span ℂ (Set.range fun x => (f x : Y → ℂ)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  let : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range f)).map L) := he.symm ▸ hf
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

private def leftCompactKernelAverageLinearWeight (h : C(A, ℂ)) :
    C(K, ℂ) →ₗ[ℂ] (A → ℂ) where
  toFun weight := leftCompactKernelAverage measure weight h
  map_add' weight weight' := by
    funext x
    change (∫ k, (weight k + weight' k) * h ((j k)⁻¹ * x) ∂measure) = _
    simp only [add_mul, Pi.add_apply, leftCompactKernelAverage]
    have hc : Continuous (fun k : K => h ((j k)⁻¹ * x)) :=
      h.continuous.comp (continuous_compactInclusion.inv.mul continuous_const)
    exact integral_add ((weight.continuous.mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) ((weight'.continuous.mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  map_smul' c weight := by
    funext x
    change (∫ k, (c * weight k) * h ((j k)⁻¹ * x) ∂measure) =
      c * ∫ k, weight k * h ((j k)⁻¹ * x) ∂measure
    simp only [mul_assoc, integral_const_mul]

private def leftCompactKernelAverageLinearKernel (weight : C(K, ℂ)) :
    C(A, ℂ) →ₗ[ℂ] (A → ℂ) where
  toFun h := leftCompactKernelAverage measure weight h
  map_add' h h' := by
    funext x
    change (∫ k, weight k * (h ((j k)⁻¹ * x) + h' ((j k)⁻¹ * x)) ∂measure) = _
    simp only [mul_add, Pi.add_apply, leftCompactKernelAverage]
    have hc : Continuous (fun k : K => (j k)⁻¹ * x) :=
      continuous_compactInclusion.inv.mul continuous_const
    exact integral_add ((weight.continuous.mul (h.continuous.comp hc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      ((weight.continuous.mul (h'.continuous.comp hc)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  map_smul' c h := by
    funext x
    change (∫ k, weight k * (c * h ((j k)⁻¹ * x)) ∂measure) =
      c * ∫ k, weight k * h ((j k)⁻¹ * x) ∂measure
    simp only [mul_left_comm (weight _) c, integral_const_mul]

omit [LocallyOfFiniteType G.X.hom] in
/-- Left compact averaging preserves right compact finiteness of the input kernel. -/
theorem isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage (weight : C(K, ℂ))
    (h : C(A, ℂ)) (hh : IsInfiniteSubgroupFiniteFunction F G K h) :
    IsInfiniteSubgroupFiniteFunction F G K (leftCompactKernelAverage measure weight h) := by
  let f (k : K) : C(A, ℂ) := ⟨fun x => h (x * j k),
    h.continuous.comp (continuous_id.mul continuous_const)⟩
  let T := Submodule.span ℂ (Set.range f)
  have : FiniteDimensional ℂ T := finiteDimensional_span_continuousMap f hh
  let L := leftCompactKernelAverageLinearKernel measure weight
  apply Submodule.finiteDimensional_of_le (S₂ := T.map L)
  apply Submodule.span_le.2
  rintro _ ⟨k, rfl⟩
  refine ⟨f k, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  funext x
  simp only [L, leftCompactKernelAverageLinearKernel, LinearMap.coe_mk, AddHom.coe_mk,
    leftCompactKernelAverage, f, ContinuousMap.coe_mk, mul_assoc]
  rfl

omit [LocallyOfFiniteType G.X.hom] in
/-- The left translate span of an averaged kernel is bounded by the left translate
span of the compact weight. -/
theorem isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage_inv
    [measure.IsMulLeftInvariant] (weight : C(K, ℂ))
    (h : C(A, ℂ))
    (hweight : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun t => weight (k⁻¹ * t)))) :
    IsInfiniteSubgroupFiniteFunction F G K
      (fun x => leftCompactKernelAverage measure weight h x⁻¹) := by
  let f (k : K) : C(K, ℂ) := ⟨fun t => weight (k⁻¹ * t),
    weight.continuous.comp (continuous_const.mul continuous_id)⟩
  let T := Submodule.span ℂ (Set.range f)
  have : FiniteDimensional ℂ T := finiteDimensional_span_continuousMap f hweight
  let L := (LinearMap.funLeft ℂ ℂ (fun x : A => x⁻¹)).comp
    (leftCompactKernelAverageLinearWeight measure h)
  apply Submodule.finiteDimensional_of_le (S₂ := T.map L)
  apply Submodule.span_le.2
  rintro _ ⟨k, rfl⟩
  refine ⟨f k, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  funext x
  change (∫ t, weight (k⁻¹ * t) * h ((j t)⁻¹ * x⁻¹) ∂measure) =
    ∫ t, weight t * h ((j t)⁻¹ * (x * j k)⁻¹) ∂measure
  rw [← integral_mul_left_eq_self (fun t => weight (k⁻¹ * t) * h ((j t)⁻¹ * x⁻¹)) k]
  simp only [inv_mul_cancel_left, map_mul, mul_inv_rev, mul_assoc]

omit [LocallyOfFiniteType G.X.hom] in
/-- The right translate span after right averaging is bounded by the left translate
span of the compact weight. -/
theorem isInfiniteSubgroupFiniteFunction_rightCompactKernelAverage
    [measure.IsMulLeftInvariant] (weight : C(K, ℂ)) (h : C(A, ℂ))
    (hweight : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun t => weight (k⁻¹ * t)))) :
    IsInfiniteSubgroupFiniteFunction F G K (rightCompactKernelAverage measure weight h) := by
  rw [rightCompactKernelAverage_eq]
  exact isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage_inv measure weight
    ⟨fun x => h x⁻¹, h.continuous.comp continuous_inv⟩ hweight

/-- Left averaging of the kernel averages the output of right convolution over the same compact. -/
theorem rightConvolution_leftCompactKernelAverage (weight : C(K, ℂ)) {h f : A → ℂ}
    (hh : Continuous h) (hs : HasCompactSupport h) (hf : Continuous f) (x : A) :
    rightConvolution F G (leftCompactKernelAverage measure weight h) f x =
      ∫ k, weight k * rightConvolution F G h f (x * j k) ∂measure := by
  let integrand (g : A) (k : K) := (weight k * h ((j k)⁻¹ * g)) * f (x * g)
  have hj : Continuous (j : K → A) := continuous_compactInclusion
  have hC : Continuous (Function.uncurry integrand) :=
    ((weight.continuous.comp continuous_snd).mul
      (hh.comp ((continuous_compactInclusion.comp continuous_snd).inv.mul continuous_fst))).mul
      (hf.comp (continuous_const.mul continuous_fst))
  have hS : HasCompactSupport (Function.uncurry integrand) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (((isCompact_range hj).mul hs.isCompact).prod isCompact_univ) ?_
    rintro ⟨z, k⟩ hz
    have hn : (weight k * h ((j k)⁻¹ * z)) * f (x * z) ≠ 0 := hz
    have hm := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
    exact ⟨⟨j k, ⟨k, rfl⟩, _, subset_tsupport _ hm, by simp⟩, mem_univ _⟩
  calc
    _ = ∫ g, (∫ k, integrand g k ∂measure) ∂dg := by
      simp only [rightConvolution, leftCompactKernelAverage, integrand, integral_mul_const]
    _ = ∫ k, (∫ g, integrand g k ∂dg) ∂measure :=
      integral_integral_swap_of_hasCompactSupport hC hS
    _ = _ := by
      unfold rightConvolution
      congr 1 with k
      rw [← integral_mul_left_eq_self («μ» := dg) (fun g => integrand g k) (j k)]
      simp only [integrand, inv_mul_cancel_left, mul_assoc, integral_const_mul]

/-- Right averaging of the kernel averages the input of right convolution by inverse
compact translates. The ambient left Haar measure is right invariant on the compact image. -/
theorem rightConvolution_rightCompactKernelAverage (weight : C(K, ℂ)) {h f : A → ℂ}
    (hh : Continuous h) (hs : HasCompactSupport h) (hf : Continuous f) (x : A) :
    rightConvolution F G (rightCompactKernelAverage measure weight h) f x =
      rightConvolution F G h
        (fun y => ∫ k, weight k * f (y * (j k)⁻¹) ∂measure) x := by
  let integrand (g : A) (k : K) := (weight k * h (g * j k)) * f (x * g)
  let shifted (g : A) (k : K) := h g * (weight k * f (x * g * (j k)⁻¹))
  have hj : Continuous (j : K → A) := continuous_compactInclusion
  have hC : Continuous (Function.uncurry integrand) :=
    ((weight.continuous.comp continuous_snd).mul
      (hh.comp (continuous_fst.mul (hj.comp continuous_snd)))).mul
      (hf.comp (continuous_const.mul continuous_fst))
  have hS : HasCompactSupport (Function.uncurry integrand) := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((hs.isCompact.mul (isCompact_range hj)).prod isCompact_univ) ?_
    rintro ⟨z, k⟩ hz
    have hn : (weight k * h (z * j k)) * f (x * z) ≠ 0 := hz
    have hm := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
    exact ⟨⟨_, subset_tsupport _ hm, j k⁻¹, ⟨k⁻¹, rfl⟩, by
      change (z * j k) * j k⁻¹ = z
      rw [map_inv, mul_inv_cancel_right]⟩,
      mem_univ _⟩
  have hC' : Continuous (Function.uncurry shifted) :=
    (hh.comp continuous_fst).mul ((weight.continuous.comp continuous_snd).mul
      (hf.comp ((continuous_const.mul continuous_fst).mul (hj.comp continuous_snd).inv)))
  have hS' : HasCompactSupport (Function.uncurry shifted) := by
    refine HasCompactSupport.of_support_subset_isCompact (hs.isCompact.prod isCompact_univ) ?_
    rintro ⟨z, k⟩ hz
    have hn : h z * (weight k * f (x * z * (j k)⁻¹)) ≠ 0 := hz
    exact ⟨subset_tsupport _ (mul_ne_zero_iff.mp hn).1, mem_univ _⟩
  have hchange (k : K) : (∫ g, integrand g k ∂dg) = ∫ g, shifted g k ∂dg := by
    let e := Homeomorph.mulRight (j k)⁻¹
    have he : MeasurePreserving e dg dg := by
      refine ⟨e.continuous.measurable, ?_⟩
      exact Langlands.CompactFactorization.map_mul_right_eq_self_of_mem dg (compactInclusion F G K).range
        (isCompact_range hj) ⟨k⁻¹, map_inv _ _⟩
    rw [← he.integral_comp e.measurableEmbedding]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g => by
      change (weight k * h (g * (j k)⁻¹ * j k)) * f (x * (g * (j k)⁻¹)) = shifted g k
      rw [inv_mul_cancel_right, ← mul_assoc, mul_comm (weight k) (h g), mul_assoc]
  calc
    _ = ∫ g, (∫ k, integrand g k ∂measure) ∂dg := by
      simp only [rightConvolution, rightCompactKernelAverage, integrand, integral_mul_const]
    _ = ∫ k, (∫ g, integrand g k ∂dg) ∂measure :=
      integral_integral_swap_of_hasCompactSupport hC hS
    _ = ∫ k, (∫ g, shifted g k ∂dg) ∂measure := by simp only [hchange]
    _ = ∫ g, (∫ k, shifted g k ∂measure) ∂dg :=
      (integral_integral_swap_of_hasCompactSupport hC' hS').symm
    _ = _ := by simp only [rightConvolution, shifted, integral_const_mul]

end Langlands.Global.AdelicGroupPoints
