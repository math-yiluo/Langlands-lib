import Langlands.Global.ArchimedeanClosedGroupOrbit
import Langlands.Global.ArchimedeanCompactKernelIntertwining
import Langlands.Global.ArchimedeanCompactCentralApproximationStatement

/-! # Finite central smoothing range and conditional exact reproduction -/

noncomputable section
universe u
open MeasureTheory Set Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions CompactKernelAverage

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Actual compact smooth kernels invariant under conjugation by the whole
standard compact subgroup. -/
def compactCentralKernels : Submodule ℂ (SmoothCompactKernel K n) where
  carrier := {κ | ∀ (k : standardInfiniteCompact K n) (g : InfiniteAdelicGL K n),
    κ.val.val (k.val⁻¹ * g * k.val) = κ.val.val g}
  zero_mem' := by intro k g; rfl
  add_mem' {κ η} hκ hη := by
    intro k g
    change κ.val.val (k.val⁻¹ * g * k.val) + η.val.val (k.val⁻¹ * g * k.val) =
      κ.val.val g + η.val.val g
    rw [hκ k g, hη k g]
  smul_mem' z κ hκ := by
    intro k g
    change z * _ = z * _
    rw [hκ k g]

variable {K n}
variable [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
variable (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]

/-- For a fixed actual vector, smoothing is a linear map of central kernels. -/
def centralSmoothingMap (f : DerivativeSmoothFunctions K n) :
    compactCentralKernels K n →ₗ[ℂ] DerivativeSmoothFunctions K n :=
  ((smoothingBilinear μ).flip f).comp (compactCentralKernels K n).subtype

@[simp]
theorem centralSmoothingMap_apply (f : DerivativeSmoothFunctions K n)
    (κ : compactCentralKernels K n) :
    centralSmoothingMap μ f κ = smoothingLM μ κ.val f := rfl

/-- Smoothing a member of the fixed closed orbit stays in that same orbit. -/
theorem smoothingLM_mem_closedGroupOrbitSpan (κ : SmoothCompactKernel K n)
    (f : DerivativeSmoothFunctions K n) {w : DerivativeSmoothFunctions K n}
    (hw : w ∈ closedGroupOrbitSpan K n f) :
    smoothingLM μ κ w ∈ closedGroupOrbitSpan K n f :=
  closedGroupOrbitSpan_le_of_mem K n f hw
    (smoothingLM_mem_closed_groupOrbit μ κ w)

/-- A finite decomposition whose pieces lie in the original closed orbit
and in actual compact types bounds the central smoothing range by the sum
of those intersections. -/
theorem range_centralSmoothingMap_le
    (f : DerivativeSmoothFunctions K n) {m : ℕ}
    (σ : Fin m → CompactType K n) (w : Fin m → DerivativeSmoothFunctions K n)
    (hw : ∀ i, w i ∈ closedGroupOrbitSpan K n f ∧
      w i ∈ compactTypeSubmodule (σ i)) (hsum : ∑ i, w i = f) :
    LinearMap.range (centralSmoothingMap μ f) ≤
      ⨆ i, closedGroupOrbitSpan K n f ⊓ compactTypeSubmodule (σ i) := by
  classical
  rintro _ ⟨κ, rfl⟩
  change smoothingLM μ κ.val f ∈ _
  have heq : smoothingLM μ κ.val f = ∑ i, smoothingLM μ κ.val (w i) := by
    rw [← hsum, map_sum]
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact (le_iSup (fun j => closedGroupOrbitSpan K n f ⊓
    compactTypeSubmodule (σ j)) i)
    ⟨smoothingLM_mem_closedGroupOrbitSpan μ κ.val f (hw i).1,
      smoothingLM_mem_isotypicSpan μ κ.val κ.property
        (σ i).toContinuousCompactRep (hw i).2⟩

/-- Finite dimension of each relevant closed-orbit compact type makes the
actual range finite-dimensional. No distribution of intersection over a sum
is used. -/
theorem finite_range_centralSmoothingMap_of_decomposition
    (f : DerivativeSmoothFunctions K n) {m : ℕ}
    (σ : Fin m → CompactType K n) (w : Fin m → DerivativeSmoothFunctions K n)
    (hw : ∀ i, w i ∈ closedGroupOrbitSpan K n f ∧
      w i ∈ compactTypeSubmodule (σ i)) (hsum : ∑ i, w i = f)
    (hfinite : ∀ i, Module.Finite ℂ
      (closedGroupOrbitSpan K n f ⊓ compactTypeSubmodule (σ i) :
        Submodule ℂ (DerivativeSmoothFunctions K n))) :
    Module.Finite ℂ (LinearMap.range (centralSmoothingMap μ f)) := by
  let S : Submodule ℂ (DerivativeSmoothFunctions K n) :=
    ⨆ i, closedGroupOrbitSpan K n f ⊓ compactTypeSubmodule (σ i)
  have : ∀ i, Module.Finite ℂ
      (closedGroupOrbitSpan K n f ⊓ compactTypeSubmodule (σ i) :
        Submodule ℂ (DerivativeSmoothFunctions K n)) := hfinite
  have : Module.Finite ℂ S := Submodule.finite_iSup _
  exact Submodule.finiteDimensional_of_le
    (S₂ := S) (range_centralSmoothingMap_le μ f σ w hw hsum)

/-- The supplied compact-central approximation theorem puts the original
vector in the closure of the actual central smoothing range. -/
theorem mem_closure_range_centralSmoothingMap
    (happrox : CompactCentralConvolutionApproximationStatement K n)
    (f : DerivativeSmoothFunctions K n) :
    f ∈ (LinearMap.range (centralSmoothingMap μ f)).topologicalClosure := by
  apply mem_closure_iff_nhds.mpr
  intro V hV
  obtain ⟨κ, _hsupport, _hnonneg, _hpositive, _hnorm, hcentral, F, hFV, hF⟩ :=
    happrox μ f V hV Set.univ Filter.univ_mem
  have hEq : F = smoothingLM μ κ f := by
    apply (toSmooth K n).injective
    apply Subtype.ext
    funext x
    exact (hF x).trans (smoothingLM_eq_rawConvolution μ κ f x).symm
  refine ⟨F, hFV, ?_⟩
  exact ⟨⟨κ, hcentral⟩, hEq.symm⟩

/-- A finite actual smoothing range is closed, so supplied central
approximation yields an actual compact smooth reproducing kernel. -/
theorem exists_central_reproducingKernel_of_finite_range
    (happrox : CompactCentralConvolutionApproximationStatement K n)
    (f : DerivativeSmoothFunctions K n)
    [Module.Finite ℂ (LinearMap.range (centralSmoothingMap μ f))] :
    ∃ κ : compactCentralKernels K n, smoothingLM μ κ.val f = f := by
  have hclosed : IsClosed
      (LinearMap.range (centralSmoothingMap μ f) :
        Set (DerivativeSmoothFunctions K n)) :=
    (LinearMap.range (centralSmoothingMap μ f)).closed_of_finiteDimensional
  have hmem := mem_closure_range_centralSmoothingMap μ happrox f
  rw [hclosed.submodule_topologicalClosure_eq] at hmem
  exact hmem

end Langlands.Global.ArchimedeanGL
