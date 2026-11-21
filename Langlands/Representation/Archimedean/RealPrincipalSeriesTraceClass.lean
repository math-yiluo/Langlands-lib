import Langlands.Analysis.CompactManifoldWeightedIntegralProof
import Langlands.Analysis.CompactSmoothKernelTraceClass
import Langlands.Analysis.TraceClassIdealProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesIntegratedKernel
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Trace class of smooth integrated operators on the real Hilbert principal series -/

noncomputable section

open Set Filter MeasureTheory
open scoped Matrix.Norms.Operator Pointwise ContDiff Manifold Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open Langlands.Analysis Langlands.Analysis.OperatorIdeals RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK borelSpaceK

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "K" => unitaryCompact ℝ n

private def compactMatrixInclusion : C(K, Mat) :=
  ⟨fun k => ((k : GL) : Mat), Units.continuous_val.comp continuous_subtype_val⟩

private theorem exists_compactMatrixCutoff : ∃ χ : Mat → ℝ, ContDiff ℝ ∞ χ ∧
    tsupport χ ⊆ {x | IsUnit x} ∧ ∀ k : K, χ (compactMatrixInclusion k) = 1 := by
  let C := Set.range (compactMatrixInclusion (n := n))
  have hC : IsCompact C := isCompact_range compactMatrixInclusion.continuous
  have hCu : C ⊆ {x : Mat | IsUnit x} := by
    rintro _ ⟨k, rfl⟩
    exact (k : GL).isUnit
  obtain ⟨S, hS, hCS, hSu⟩ := exists_compact_between hC Units.isOpen hCu
  obtain ⟨χ, hχ, -, hSupport, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := ⊤) isOpen_interior hC.isClosed hCS
  refine ⟨χ, hχ, ?_, fun k => (hone _).mp ⟨k, rfl⟩⟩
  change closure (Function.support χ) ⊆ _
  rw [hSupport]
  exact (closure_minimal interior_subset hS.isClosed).trans hSu

private def cutoffKernelIntegrand (χ : Mat → ℝ) (φ : Mat → ℂ) (p : (Mat × Mat) × Mat) : ℂ :=
  (χ p.1.1 : ℂ) * φ (Ring.inverse p.1.1 * p.2 * p.1.2)

private theorem contDiff_cutoffKernelIntegrand {χ : Mat → ℝ} {φ : Mat → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hχu : tsupport χ ⊆ {x | IsUnit x}) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (cutoffKernelIntegrand χ φ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1.1 ∈ tsupport χ
  · have hu : IsUnit p.1.1 := hχu hp
    have hi := contDiffAt_ringInverse (n := ∞) ℝ hu.unit
    rw [IsUnit.unit_spec] at hi
    have hi' : ContDiffAt ℝ ∞ (fun q : (Mat × Mat) × Mat => Ring.inverse q.1.1) p :=
      hi.comp p (contDiff_fst.comp contDiff_fst).contDiffAt
    have hχ' := Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (hχ.contDiffAt.comp p (contDiff_fst.comp contDiff_fst).contDiffAt)
    exact hχ'.mul (hφ.contDiffAt.comp p ((hi'.mul contDiff_snd.contDiffAt).mul
      (contDiff_snd.comp contDiff_fst).contDiffAt))
  · apply contDiffAt_const.congr_of_eventuallyEq
    have hC : Continuous (fun q : (Mat × Mat) × Mat => q.1.1) := continuous_fst.comp continuous_fst
    filter_upwards [hC.continuousAt.preimage_mem_nhds
      ((isClosed_tsupport χ).isOpen_compl.mem_nhds hp)] with q hq
    change cutoffKernelIntegrand χ φ q = 0
    unfold cutoffKernelIntegrand
    rw [image_eq_zero_of_notMem_tsupport hq, Complex.ofReal_zero, zero_mul]

private def triangularMatrix (g : GL) : Mat :=
  ((g * (((compactFactor g)⁻¹ : K) : GL) : GL) : Mat)

private theorem continuous_triangularMatrix : Continuous (triangularMatrix (n := n)) :=
  Units.continuous_val.comp (continuous_id.mul (continuous_subtype_val.comp compactFactor.continuous.inv))

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [IsFiniteMeasureOnCompacts μ]
  (a : Fin n → ℂ) (f : C(Langlands.GeneralLinear n ℝ, ℂ))

private theorem principalSeriesCompactKernel_apply (hf : HasCompactSupport f) (x y : K) :
    principalSeriesCompactKernel μ a f (x, y) =
      ∫ g, compactWeight a g * f ((x : GL)⁻¹ * g * ((((compactFactor g)⁻¹ : K) * y) : GL)) ∂μ := by
  unfold principalSeriesCompactKernel
  rw [compactPictureKernel_apply _ _ _ _ _ _ _ hf]
  rfl

omit [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)] in
private theorem support_principalSeriesCompactKernel_integrand (x y : K) (g : GL)
    (h : f ((x : GL)⁻¹ * g * ((((compactFactor g)⁻¹ : K) * y) : GL)) ≠ 0) :
    g ∈ (K : Set GL) * tsupport f * (K : Set GL) := by
  let r : K := ((compactFactor g)⁻¹ : K) * y
  let t : GL := (x : GL)⁻¹ * g * (r : GL)
  have ht : t ∈ tsupport f := subset_tsupport f h
  have he : (x : GL) * t * ((r⁻¹ : K) : GL) = g := by
    change (x : GL) * t * (r : GL)⁻¹ = g
    dsimp only [t]
    group
  rw [← he]
  exact Set.mul_mem_mul (Set.mul_mem_mul x.2 ht) (r⁻¹ : K).2

set_option maxHeartbeats 1100000 in
/-- Smooth compactly supported tests give a compact-picture kernel with a joint smooth
extension in ambient real matrix coordinates. -/
theorem exists_smooth_extension_principalSeriesCompactKernel (hf : HasCompactSupport f)
    (hφ : ContDiff ℝ ∞ (unitsExtension f)) :
    ∃ F : Mat × Mat → ℂ, ContDiff ℝ ∞ F ∧ ∀ x y : K,
      principalSeriesCompactKernel μ a f (x, y) = F (compactMatrixInclusion x, compactMatrixInclusion y) := by
  obtain ⟨χ, hχ, hχu, hχone⟩ := exists_compactMatrixCutoff (n := n)
  let S := (K : Set GL) * tsupport f * (K : Set GL)
  have hK : IsCompact (K : Set GL) := isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace K))
  have hS : IsCompact S := (hK.mul hf).mul hK
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  let ν₀ : Measure GL := μ.restrict S
  let : IsFiniteMeasure ν₀ := ⟨by simpa only [ν₀, Measure.restrict_apply_univ] using hS.measure_lt_top (μ := μ)⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let ν : Measure S := ν₀.comap Subtype.val
  let w : C(S, ℂ) := (compactWeight a).comp ⟨Subtype.val, continuous_subtype_val⟩
  let j : C(S, Mat) := ⟨fun g => triangularMatrix g.1,
    continuous_triangularMatrix.comp continuous_subtype_val⟩
  let h := cutoffKernelIntegrand χ (unitsExtension f)
  have hh : ContMDiff (𝓘(ℝ, Mat × Mat).prod 𝓘(ℝ, Mat)) 𝓘(ℝ, ℂ) ∞ h := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (contDiff_cutoffKernelIntegrand hχ hχu hφ).contMDiff
  let F : Mat × Mat → ℂ := fun p => ∫ g, h (p, j g) • w g ∂ν
  have hF : ContDiff ℝ ∞ F := (compactManifoldWeightedIntegral S (Mat × Mat) (Mat × Mat)
    Mat Mat ℂ ν w j h hh).2.contDiff
  refine ⟨F, hF, ?_⟩
  intro x y
  let v := fun g => compactWeight a g * f ((x : GL)⁻¹ * g * ((((compactFactor g)⁻¹ : K) * y) : GL))
  rw [principalSeriesCompactKernel_apply μ a f hf]
  have hv (g : S) : h ((compactMatrixInclusion x, compactMatrixInclusion y), j g) • w g = v g.1 := by
    simp only [h, cutoffKernelIntegrand, hχone, Complex.ofReal_one, one_mul, smul_eq_mul, w,
      ContinuousMap.comp_apply]
    change unitsExtension f (Ring.inverse (((x : GL) : Mat)) * triangularMatrix g.1 * ((y : GL) : Mat)) *
      compactWeight a g.1 = v g.1
    rw [Ring.inverse_unit]
    have he : (((x : GL)⁻¹ : GL) : Mat) * triangularMatrix g.1 * ((y : GL) : Mat) =
        (((x : GL)⁻¹ * g.1 * ((((compactFactor g.1)⁻¹ : K) * y) : GL) : GL) : Mat) := by
      simp only [triangularMatrix, Units.val_mul, mul_assoc]
    rw [he, unitsExtension_val]
    exact mul_comm _ _
  have hFval : F (compactMatrixInclusion x, compactMatrixInclusion y) = ∫ g : S, v g.1 ∂ν :=
    integral_congr_ae (Eventually.of_forall hv)
  rw [hFval]
  change (∫ g, v g ∂μ) = ∫ g : S, v g.1 ∂(ν₀.comap Subtype.val)
  rw [integral_subtype_comap hSm v]
  change (∫ g, v g ∂μ) = ∫ g in S, v g ∂(μ.restrict S)
  rw [Measure.restrict_restrict hSm, inter_self]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro g hg
  have hz : f ((x : GL)⁻¹ * g * ((((compactFactor g)⁻¹ : K) * y) : GL)) = 0 := by
    by_contra hn
    exact hg (support_principalSeriesCompactKernel_integrand f x y g hn)
  change compactWeight a g * _ = 0
  rw [hz, mul_zero]

/-- A joint smooth extension of the integrated compact-picture kernel in
ambient real matrix coordinates. -/
def principalSeriesCompactKernelSmoothExtension (hf : HasCompactSupport f)
    (hφ : ContDiff ℝ ∞ (unitsExtension f)) : Mat × Mat → ℂ :=
  (exists_smooth_extension_principalSeriesCompactKernel μ a f hf hφ).choose

local instance (d : ℕ) : SecondCountableTopology (Langlands.GeneralLinear d ℝ) :=
  Units.isOpenEmbedding_val.secondCountableTopology

local instance (d : ℕ) : SecondCountableTopology (unitaryCompact ℝ d) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

variable [SFinite μ] [μ.IsMulRightInvariant] [μ.IsMulLeftInvariant] (e : Fin n → Fin 2)

/-- A smoothly integrated real principal-series operator is trace class on the Hilbert completion. -/
theorem isTraceClass_integrated (hf : HasCompactSupport f) (hφ : ContDiff ℝ ∞ (unitsExtension f))
    (T : Hilbert a e →L[ℂ] Hilbert a e)
    (hT : ∀ x, T x = ∫ g, f g • representation a e g x ∂μ) : IsTraceClass T := by
  let L := (ContinuousMap.toLp 2 (haarK n) ℂ).comp
    (continuousKernelProfile (haarK n) (principalSeriesCompactKernel μ a f))
  let J := (closureSubmodule a e).subtypeL
  let P := (closureSubmodule a e).orthogonalProjectionOnto
  let F := principalSeriesCompactKernelSmoothExtension μ a f hf hφ
  obtain ⟨hF, hEq⟩ := (exists_smooth_extension_principalSeriesCompactKernel μ a f hf hφ).choose_spec
  have hL : IsTraceClass L := isTraceClass_continuousKernelOperator_of_smooth_extension
    (haarK n) (principalSeriesCompactKernel μ a f) compactMatrixInclusion compactMatrixInclusion F hF hEq
  have hInt : J.comp T = L.comp J := integrated_eq_compactKernel μ a e f hf T hT
  have hT' : T = (P.comp L).comp J := by
    rw [ContinuousLinearMap.comp_assoc, ← hInt]
    apply ContinuousLinearMap.ext
    intro v
    exact ((closureSubmodule a e).orthogonalProjectionOnto_mem_subspace_eq_self (T v)).symm
  rw [hT']
  exact isTraceClass_sandwich L P J hL

end Langlands.Archimedean.RealPrincipalSeriesHilbert
