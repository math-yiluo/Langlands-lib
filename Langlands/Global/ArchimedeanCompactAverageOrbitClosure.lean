import Langlands.Global.ArchimedeanCompactAverageContinuity
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Closed compact-orbit containment of the actual weighted average -/

noncomputable section
universe u v
open MeasureTheory Set Filter Topology
open scoped BigOperators
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactWeightedAverage

open DerivativeSmoothFunctions

private theorem integral_mem_closed_submodule
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (M : Submodule ℂ E) (hM : IsClosed (M : Set E))
    {F : Ω → E} (hF : Integrable F μ) (hm : ∀ᵐ k ∂μ, F k ∈ M) :
    (∫ k, F k ∂μ) ∈ M := by
  have : IsClosed (M : Set E) := hM
  apply (Submodule.Quotient.mk_eq_zero M).mp
  change M.mkQL (∫ k, F k ∂μ) = 0
  rw [← M.mkQL.integral_comp_comm hF]
  apply integral_eq_zero_of_ae
  exact hm.mono fun k hk => (Submodule.Quotient.mk_eq_zero M).mpr hk

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

private def finiteCoordinates (I : Finset (CoordinateIndex (K := K) (n := n))) :
    DerivativeSmoothFunctions K n →L[ℂ] (∀ i : I, C(i.val.2.val, ℂ)) where
  toFun f i := compactCoordinates f i
  map_add' f g := by
    ext i x
    change DerivativeSmoothFunctions.derivativeCoordinates K n (f + g) i.val.1 x =
      DerivativeSmoothFunctions.derivativeCoordinates K n f i.val.1 x +
        DerivativeSmoothFunctions.derivativeCoordinates K n g i.val.1 x
    rw [map_add]
    rfl
  map_smul' z f := by
    ext i x
    change DerivativeSmoothFunctions.derivativeCoordinates K n (z • f) i.val.1 x =
      z • DerivativeSmoothFunctions.derivativeCoordinates K n f i.val.1 x
    rw [map_smul]
    rfl
  cont := by
    apply continuous_pi
    intro i
    exact (ContinuousMap.continuous_restrict i.val.2.val).comp
      (DerivativeSmoothFunctions.derivativeCLM K n i.val.1).continuous

variable [MeasurableSpace (standardInfiniteCompact K n)]
  [BorelSpace (standardInfiniteCompact K n)]
variable (ν : Measure (standardInfiniteCompact K n)) [IsFiniteMeasure ν]
variable (w : C(standardInfiniteCompact K n, ℂ))

private theorem finiteOrbit_integrable
    (I : Finset (CoordinateIndex (K := K) (n := n)))
    (f : DerivativeSmoothFunctions K n) :
    Integrable (fun k : standardInfiniteCompact K n =>
      w k • finiteCoordinates I (compactAction K n k f)) ν := by
  classical
  have hk : Continuous (fun k : standardInfiniteCompact K n =>
      compactAction K n k f) := by
    have hp : Continuous (fun k : standardInfiniteCompact K n => (k, f)) :=
      continuous_id.prodMk continuous_const
    exact (continuous_compactAction K n).comp
      (f := fun k : standardInfiniteCompact K n => (k, f)) hp
  have hc : Continuous (fun k : standardInfiniteCompact K n =>
      finiteCoordinates I (compactAction K n k f)) :=
    (finiteCoordinates I).continuous.comp hk
  have h : Continuous (fun k : standardInfiniteCompact K n =>
      w k • finiteCoordinates I (compactAction K n k f)) :=
    w.continuous.smul hc
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem finiteCoordinates_average
    (I : Finset (CoordinateIndex (K := K) (n := n)))
    (f : DerivativeSmoothFunctions K n) :
    finiteCoordinates I (averageCLM ν w f) =
      ∫ k : standardInfiniteCompact K n,
        w k • finiteCoordinates I (compactAction K n k f) ∂ν := by
  classical
  ext i x
  let L : (∀ j : I, C(j.val.2.val, ℂ)) →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ x).comp (ContinuousLinearMap.proj i)
  change compactCoordinates (averageCLM ν w f) i.val x =
    L (∫ k : standardInfiniteCompact K n,
      w k • finiteCoordinates I (compactAction K n k f) ∂ν)
  rw [← L.integral_comp_comm (finiteOrbit_integrable ν w I f)]
  change (envelopingAction K n i.val.1
      (averageSmoothLM ν w (DerivativeSmoothFunctions.toSmooth K n f))).val x =
    ∫ k : standardInfiniteCompact K n,
      w k * (envelopingAction K n i.val.1
        (smoothRightAction K n k.val (DerivativeSmoothFunctions.toSmooth K n f))).val x ∂ν
  exact envelopingDerivative_average ν i.val.1 w
    (DerivativeSmoothFunctions.toSmooth K n f) x

private theorem finiteCoordinates_average_mem
    (I : Finset (CoordinateIndex (K := K) (n := n)))
    (f : DerivativeSmoothFunctions K n) :
    finiteCoordinates I (averageCLM ν w f) ∈
      ((Submodule.span ℂ (range fun k : standardInfiniteCompact K n =>
        compactAction K n k f)).map (finiteCoordinates I).toLinearMap).topologicalClosure := by
  classical
  rw [finiteCoordinates_average ν w I f]
  apply integral_mem_closed_submodule _
    (Submodule.isClosed_topologicalClosure _) (finiteOrbit_integrable ν w I f)
  apply Filter.Eventually.of_forall
  intro k
  apply Submodule.smul_mem
  apply Submodule.le_topologicalClosure
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)

/-- The genuine smooth weighted average belongs to the closed complex span of
the actual compact right orbit, without integrating in the smooth carrier. -/
theorem average_mem_closed_compactOrbit (f : DerivativeSmoothFunctions K n) :
    averageCLM ν w f ∈
      (Submodule.span ℂ (range fun k : standardInfiniteCompact K n =>
        compactAction K n k f)).topologicalClosure := by
  classical
  let M := Submodule.span ℂ (range fun k : standardInfiniteCompact K n =>
    compactAction K n k f)
  change averageCLM ν w f ∈ closure (M : Set (DerivativeSmoothFunctions K n))
  rw [isInducing_compactCoordinates.closure_eq_preimage_closure_image]
  apply mem_closure_of_finite_coordinate_images
  intro I
  have h := finiteCoordinates_average_mem ν w I f
  change (fun i : I => compactCoordinates (averageCLM ν w f) i.val) ∈
    closure ((fun x : DerivativeSmoothFunctions K n =>
      fun i : I => compactCoordinates x i.val) ''
        (M : Set (DerivativeSmoothFunctions K n))) at h
  simpa only [image_image] using h

end Langlands.Global.ArchimedeanGL.CompactWeightedAverage
