import Langlands.Global.ArchimedeanCompactIndexDerivatives
import Langlands.Global.ArchimedeanCompactTypes
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Compact-index averaging approximates in the genuine derivative topology -/

noncomputable section
universe u
open MeasureTheory Set Filter Topology Metric
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactIndexAverage

open DerivativeSmoothFunctions

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

private abbrev CoordinateIndex :=
  EnvelopingAlgebra K n × {s : Set (InfiniteAdelicGL K n) // IsCompact s}

private instance coordinateIndex_compactSpace (i : CoordinateIndex (K := K) (n := n)) :
    CompactSpace i.2.val :=
  isCompact_iff_compactSpace.mp i.2.property

private def compactCoordinates (f : DerivativeSmoothFunctions K n)
    (i : CoordinateIndex (K := K) (n := n)) : C(i.2.val, ℂ) :=
  (DerivativeSmoothFunctions.derivativeCoordinates K n f i.1).restrict i.2.val

private theorem isInducing_compactCoordinates :
    IsInducing (compactCoordinates (K := K) (n := n)) := by
  apply isInducing_iff_nhds.mpr
  intro f
  rw [DerivativeSmoothFunctions.nhds_eq_iInf]
  have h (a : EnvelopingAlgebra K n) :=
    ContinuousMap.nhds_compactOpen_eq_iInf_nhds_induced
      (DerivativeSmoothFunctions.derivativeCoordinates K n f a)
  simp_rw [h, Filter.comap_iInf, Filter.comap_comap]
  simp only [nhds_pi, Filter.pi, Filter.comap_iInf, Filter.comap_comap,
    CoordinateIndex, iInf_prod, iInf_subtype']
  rfl


private def coordinateCLM (i : CoordinateIndex (K := K) (n := n)) :
    DerivativeSmoothFunctions K n →L[ℂ] C(i.2.val, ℂ) where
  toFun f := compactCoordinates f i
  map_add' f g := by
    ext x
    change derivativeCoordinates K n (f + g) i.1 x =
      derivativeCoordinates K n f i.1 x + derivativeCoordinates K n g i.1 x
    rw [map_add]
    rfl
  map_smul' z f := by
    ext x
    change derivativeCoordinates K n (z • f) i.1 x =
      z • derivativeCoordinates K n f i.1 x
    rw [map_smul]
    rfl
  cont := (ContinuousMap.continuous_restrict i.2.val).comp
    (derivativeCLM K n i.1).continuous

private theorem continuous_rightOrbit (f : DerivativeSmoothFunctions K n) :
    Continuous (fun g : InfiniteAdelicGL K n => rightAction K n g f) := by
  exact (continuous_rightAction K n).comp
    (f := fun g : InfiniteAdelicGL K n => (g, f))
    (continuous_id.prodMk continuous_const)

private def coordinateOrbit (i : CoordinateIndex (K := K) (n := n))
    (f : DerivativeSmoothFunctions K n) :
    C(InfiniteAdelicGL K n, C(i.2.val, ℂ)) :=
  ⟨fun g => coordinateCLM i (rightAction K n g f),
    (coordinateCLM i).continuous.comp
      (f := fun g : InfiniteAdelicGL K n => rightAction K n g f)
      (continuous_rightOrbit f)⟩

private theorem coordinateOrbit_one (i : CoordinateIndex (K := K) (n := n))
    (f : DerivativeSmoothFunctions K n) :
    coordinateOrbit i f 1 = coordinateCLM i f := by
  change coordinateCLM i (rightAction K n 1 f) = coordinateCLM i f
  simp

variable {J : Type u} [TopologicalSpace J] [T2Space J] [CompactSpace J]
  [MeasurableSpace J] [BorelSpace J]
variable (r : C(J, InfiniteAdelicGL K n))
variable (ν : Measure J) [IsFiniteMeasure ν] (w : C(J, ℂ))

omit [T2Space J] in
private theorem coordinateOrbit_integrable
    (i : CoordinateIndex (K := K) (n := n))
    (f : DerivativeSmoothFunctions K n) :
    Integrable (fun j => w j • coordinateCLM i (rightAction K n (r j) f)) ν := by
  have h : Continuous (fun j => w j • coordinateCLM i (rightAction K n (r j) f)) :=
    w.continuous.smul ((coordinateOrbit i f).continuous.comp r.continuous)
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem coordinate_average
    (i : CoordinateIndex (K := K) (n := n))
    (f : DerivativeSmoothFunctions K n) :
    coordinateCLM i (averageLM r ν w f) =
      ∫ j, w j • coordinateCLM i (rightAction K n (r j) f) ∂ν := by
  ext x
  let L : C(i.2.val, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
  change compactCoordinates (averageLM r ν w f) i x =
    L (∫ j, w j • coordinateCLM i (rightAction K n (r j) f) ∂ν)
  rw [← L.integral_comp_comm (coordinateOrbit_integrable r ν w i f)]
  exact envelopingDerivative_average r ν i.1 w (toSmooth K n f) x

private def finiteCoordinates
    (I : Finset (CoordinateIndex (K := K) (n := n))) :
    DerivativeSmoothFunctions K n →L[ℂ] (∀ i : I, C(i.val.2.val, ℂ)) where
  toFun f i := coordinateCLM i.val f
  map_add' f g := by
    ext i x
    exact congrArg (fun h : C(i.val.2.val, ℂ) => h x) ((coordinateCLM i.val).map_add f g)
  map_smul' z f := by
    ext i x
    exact congrArg (fun h : C(i.val.2.val, ℂ) => h x) ((coordinateCLM i.val).map_smul z f)
  cont := continuous_pi fun i => (coordinateCLM i.val).continuous

omit [T2Space J] in
private theorem finiteOrbit_integrable
    (I : Finset (CoordinateIndex (K := K) (n := n)))
    (f : DerivativeSmoothFunctions K n) :
    Integrable (fun j => w j • finiteCoordinates I (rightAction K n (r j) f)) ν := by
  classical
  have h : Continuous (fun j => w j • finiteCoordinates I (rightAction K n (r j) f)) :=
    w.continuous.smul ((finiteCoordinates I).continuous.comp
      ((continuous_rightOrbit f).comp r.continuous))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem finiteCoordinates_average
    (I : Finset (CoordinateIndex (K := K) (n := n)))
    (f : DerivativeSmoothFunctions K n) :
    finiteCoordinates I (averageLM r ν w f) =
      ∫ j, w j • finiteCoordinates I (rightAction K n (r j) f) ∂ν := by
  classical
  ext i x
  let L : (∀ j : I, C(j.val.2.val, ℂ)) →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ x).comp (ContinuousLinearMap.proj i)
  change compactCoordinates (averageLM r ν w f) i.val x =
    L (∫ j, w j • finiteCoordinates I (rightAction K n (r j) f) ∂ν)
  rw [← L.integral_comp_comm (finiteOrbit_integrable r ν w I f)]
  exact envelopingDerivative_average r ν i.val.1 w (toSmooth K n f) x

private theorem integral_mem_closed_submodule
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (M : Submodule ℂ E) (hM : IsClosed (M : Set E))
    {F : Ω → E} (hF : Integrable F μ) (hm : ∀ᵐ j ∂μ, F j ∈ M) :
    (∫ j, F j ∂μ) ∈ M := by
  have : IsClosed (M : Set E) := hM
  apply (Submodule.Quotient.mk_eq_zero M).mp
  change M.mkQL (∫ j, F j ∂μ) = 0
  rw [← M.mkQL.integral_comp_comm hF]
  apply integral_eq_zero_of_ae
  exact hm.mono fun j hj => (Submodule.Quotient.mk_eq_zero M).mpr hj

private theorem mem_closure_of_finite_coordinate_images
    {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    {S : Set (∀ i, E i)} {x : ∀ i, E i}
    (h : ∀ I : Finset ι, (fun i : I => x i) ∈
      closure ((fun y : ∀ i, E i => fun i : I => y i) '' S)) :
    x ∈ closure S := by
  classical
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hU
  have hT : Set.pi univ (fun i : I => t i) ∈ 𝓝 (fun i : I => x i) := by
    rw [nhds_pi]
    exact Filter.pi_mem_pi Set.finite_univ fun i _ => ht i
  obtain ⟨y, hyt, hy⟩ := mem_closure_iff_nhds.mp (h I) _ hT
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨z, hsub ?_, hz⟩
  intro i hi
  exact hyt ⟨i, hi⟩ (mem_univ _)

/-- The actual compact-index average is in the closed span of its actual
right-translation family, in the full genuine derivative topology. -/
theorem average_mem_closed_orbit (f : DerivativeSmoothFunctions K n) :
    averageLM r ν w f ∈
      (Submodule.span ℂ (range fun j => rightAction K n (r j) f)).topologicalClosure := by
  classical
  let M := Submodule.span ℂ (range fun j => rightAction K n (r j) f)
  change averageLM r ν w f ∈ closure (M : Set (DerivativeSmoothFunctions K n))
  rw [isInducing_compactCoordinates.closure_eq_preimage_closure_image]
  apply mem_closure_of_finite_coordinate_images
  intro I
  have h : finiteCoordinates I (averageLM r ν w f) ∈
      (M.map (finiteCoordinates I).toLinearMap).topologicalClosure := by
    rw [finiteCoordinates_average r ν w I f]
    apply integral_mem_closed_submodule _
      (Submodule.isClosed_topologicalClosure _) (finiteOrbit_integrable r ν w I f)
    apply Filter.Eventually.of_forall
    intro j
    apply Submodule.smul_mem
    apply Submodule.le_topologicalClosure
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, rfl⟩)
  change (fun i : I => compactCoordinates (averageLM r ν w f) i.val) ∈
    closure ((fun x : DerivativeSmoothFunctions K n =>
      fun i : I => compactCoordinates x i.val) ''
        (M : Set (DerivativeSmoothFunctions K n))) at h
  simpa only [image_image] using h

omit [T2Space J] in
private theorem norm_integral_average_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : C(J, E)) (x : E) (ε : ℝ)
    (hw : (∫ j, w j ∂ν) = 1) (hnorm : (∫ j, ‖w j‖ ∂ν) = 1)
    (hF : ∀ j, ‖F j - x‖ ≤ ε) :
    ‖(∫ j, w j • F j ∂ν) - x‖ ≤ ε := by
  have h1 : Integrable (fun j => w j • F j) ν :=
    (w.continuous.smul F.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun j => w j • x) ν :=
    (w.continuous.smul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : (∫ j, w j • F j ∂ν) - x = ∫ j, w j • (F j - x) ∂ν := by
    simp_rw [smul_sub]
    rw [integral_sub h1 h2, integral_smul_const, hw, one_smul]
  rw [heq]
  have hb : Integrable (fun j => ‖w j‖ * ε) ν :=
    (w.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    ‖∫ j, w j • (F j - x) ∂ν‖ ≤ ∫ j, ‖w j‖ * ε ∂ν :=
      norm_integral_le_of_norm_le hb
        (Eventually.of_forall fun j => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hF j) (norm_nonneg _))
    _ = ε := by rw [integral_mul_const, hnorm, one_mul]

/-- One identity neighborhood works for every compact-index average with both
complex integral and integral of the absolute weight equal to one. -/
theorem exists_average_neighborhood
    (f : DerivativeSmoothFunctions K n) (V : Set (DerivativeSmoothFunctions K n))
    (hV : V ∈ 𝓝 f) :
    ∃ U : Set (InfiniteAdelicGL K n), U ∈ 𝓝 (1 : InfiniteAdelicGL K n) ∧
      ∀ (J : Type u) [TopologicalSpace J] [T2Space J] [CompactSpace J]
        [MeasurableSpace J] [BorelSpace J]
        (r : C(J, InfiniteAdelicGL K n)) (ν : Measure J) [IsFiniteMeasure ν]
        (w : C(J, ℂ)),
        (∀ j, r j ∈ U) → (∫ j, w j ∂ν) = 1 → (∫ j, ‖w j‖ ∂ν) = 1 →
        averageLM r ν w f ∈ V := by
  classical
  rw [isInducing_compactCoordinates.nhds_eq_comap] at hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
  rw [nhds_pi] at hW
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hW
  choose ε hε hball using fun i : I => Metric.mem_nhds_iff.mp (ht i)
  let U : Set (InfiniteAdelicGL K n) := ⋂ i : I,
    (fun g => coordinateCLM i (rightAction K n g f)) ⁻¹'
      ball (coordinateCLM i f) (ε i / 2)
  refine ⟨U, ?_, ?_⟩
  · apply Filter.iInter_mem.mpr
    intro i
    have hc : Continuous (fun g : InfiniteAdelicGL K n =>
        coordinateCLM i (rightAction K n g f)) :=
      (coordinateOrbit (i : CoordinateIndex (K := K) (n := n)) f).continuous
    have he : coordinateCLM i (rightAction K n 1 f) = coordinateCLM i f := by
      simp
    exact hc.continuousAt (he ▸ ball_mem_nhds _ (half_pos (hε i)))
  · intro J _ _ _ _ _ r ν _ w hr hw hnorm
    apply hWV
    apply hsub
    intro i hi
    let j : I := ⟨i, hi⟩
    apply hball j
    rw [mem_ball, dist_eq_norm]
    have hb : ‖coordinateCLM i (averageLM r ν w f) - coordinateCLM i f‖ ≤ ε j / 2 := by
      rw [coordinate_average r ν w i f]
      let F : C(J, C(i.2.val, ℂ)) :=
        (coordinateOrbit i f).comp r
      apply norm_integral_average_sub_le ν w F (coordinateCLM i f) (ε j / 2) hw hnorm
      intro k
      change ‖coordinateCLM i (rightAction K n (r k) f) - coordinateCLM i f‖ ≤ ε j / 2
      simpa only [dist_eq_norm] using (mem_ball.mp (mem_iInter.mp (hr k) j)).le
    exact hb.trans_lt (half_lt_self (hε j))

end Langlands.Global.ArchimedeanGL.CompactIndexAverage
