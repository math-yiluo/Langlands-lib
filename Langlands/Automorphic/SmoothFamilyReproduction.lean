import Langlands.Automorphic.CuspidalAdmissible.Reproduction
import Langlands.Global.ArchimedeanSmoothFamilyOrbit
import Langlands.Global.ArchimedeanSmoothFamilyCompactProjection
import Langlands.Global.ArchimedeanCenterQuotientOrbit
import Langlands.Global.ArchimedeanSeparateJointFiniteProof

/-! # One central smoothing kernel for a whole archimedean family -/

noncomputable section
universe u w
open MeasureTheory Filter Topology TopologicalSpace
open scoped Classical
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.SmoothFamily

open DerivativeSmoothFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {ι : Type w}

local notation "V" => SmoothFamily F n ι
local notation "U" => EnvelopingAlgebra F n
local notation "D" => DerivativeSmoothFunctions F n
local notation "ρ" => compactRepresentation (F := F) (n := n) (ι := ι)

variable [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
variable (μ : Measure (InfiniteAdelicGL F n)) [μ.IsHaarMeasure]

/-- The simultaneous compact-kernel action on the archimedean smooth family. -/
def smoothingLM (κ : SmoothCompactKernel F n) : V →ₗ[ℂ] V :=
  averageLM (CompactKernelAverage.inclusion κ) (CompactKernelAverage.measure μ κ)
    (CompactKernelAverage.weight κ)

@[simp]
theorem smoothingLM_apply (κ : SmoothCompactKernel F n) (f : V) (i : ι) :
    smoothingLM μ κ f i = CompactKernelAverage.smoothingLM μ κ (f i) := rfl

private def smoothingIntertwining (κ : compactCentralKernels F n) :
    Representation.IntertwiningMap ρ ρ :=
  (smoothingLM μ κ.val).intertwiningMap_of_isIntertwiningMap _ _
    (fun k f => funext fun i =>
      CompactKernelAverage.smoothingLM_compactAction μ κ.val κ.property k (f i))

variable (J : Ideal (EnvelopingCenter F n))
variable [Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ)]

omit [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)] in
private theorem isJointFinite_of_source {m : ℕ}
    {σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)}
    (j : σ.IntertwiningMap ρ) (hJ : ∀ z ∈ J, ∀ v, (z : U) • j v = 0)
    (v : Fin m → ℂ) (i : ι) : IsJointFinite F n (toSmooth F n (j v i)) := by
  let p : Representation.IntertwiningMap ρ (compactAction F n) :=
    (LinearMap.proj i).intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  have : Module.Finite ℂ j.range.toSubmodule := Module.Finite.range j.toLinearMap
  have hfinite : Langlands.FiniteVectors.IsFiniteVector ρ (j v) :=
    Langlands.FiniteVectors.isFiniteVector_of_mem ρ j.range ⟨v, rfl⟩
  have hc : Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype)
      (toSmooth F n (j v i)) :=
    Langlands.FiniteVectors.IsFiniteVector.map (compactActionEquiv F n).toIntertwiningMap
      (Langlands.FiniteVectors.IsFiniteVector.map p hfinite)
  have hz : IsCenterFinite F n (toSmooth F n (j v i)) := by
    apply isCenterFinite_of_finite_quotient_annihilates F n J inferInstance
    intro z hz
    change envelopingAction F n (z : U) (toSmooth F n (j v i)) = 0
    have h := congrArg (fun f : V => toSmooth F n (f i)) (hJ z hz v)
    simpa only [Pi.smul_apply, enveloping_smul_eq_operator, toSmooth_operator,
      Pi.zero_apply, map_zero] using h
  exact separateJointFinite F n _ hz (compactGroupFiniteDifferential F n _ hc)

private theorem smoothingLM_mem_closure {m : ℕ}
    {σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)}
    (j : σ.IntertwiningMap ρ) (hJ : ∀ z ∈ J, ∀ v, (z : U) • j v = 0)
    (κ : SmoothCompactKernel F n) (v : Fin m → ℂ) :
    smoothingLM μ κ (j v) ∈ ((envelopingSpan j).restrictScalars ℂ).topologicalClosure := by
  apply averageLM_mem_topologicalClosure
  intro k
  apply rightRepresentation_mem_closure _ (j v) (isJointFinite_of_source J j hJ v)
  intro l a
  exact compactRepresentation_mem_envelopingSpan j l
    ((envelopingSpan j).smul_mem a (mem_envelopingSpan j v))

section ContinuousSource

variable [MeasurableSpace (standardInfiniteCompact F n)] [BorelSpace (standardInfiniteCompact F n)]

set_option maxHeartbeats 600000 in
private theorem exists_centralKernel_reproduces_of_continuous
    (ν : Measure (standardInfiniteCompact F n)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (τ : ContinuousCompactRep F n)
    (j : τ.toRepresentation.IntertwiningMap ρ) (hJ : ∀ z ∈ J, ∀ v, (z : U) • j v = 0) :
    ∃ κ : compactCentralKernels F n, ∀ v i,
      CompactKernelAverage.smoothingLM μ κ.val (j v i) = j v i := by
  obtain ⟨E, hE, hcover⟩ := exists_finite_cover_of_closure_intertwiner_values ν τ τ j J hJ
  let Φ : compactCentralKernels F n →ₗ[ℂ] (Fin τ.dim × ι → D) :=
    LinearMap.pi fun p => ArchimedeanGL.centralSmoothingMap μ (j (Pi.single p.1 1) p.2)
  let ψ : (Fin τ.dim → E) →ₗ[ℂ] (Fin τ.dim × ι → D) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (E.subtype.comp (LinearMap.proj p.1))
  have hle : LinearMap.range Φ ≤ LinearMap.range ψ := by
    rintro _ ⟨κ, rfl⟩
    let S := (smoothingIntertwining μ κ).comp j
    have hS (v : Fin τ.dim → ℂ) : S v ∈ E :=
      hcover S (smoothingLM_mem_closure μ J j hJ κ.val) v
    exact ⟨fun a => ⟨S (Pi.single a 1), hS _⟩, rfl⟩
  have : Module.Finite ℂ (LinearMap.range Φ) := Submodule.finiteDimensional_of_le hle
  have hclosed : IsClosed (LinearMap.range Φ : Set (Fin τ.dim × ι → D)) :=
    (LinearMap.range Φ).closed_of_finiteDimensional
  let f (p : Fin τ.dim × ι) := j (Pi.single p.1 1) p.2
  have hmem : f ∈ closure (LinearMap.range Φ : Set (Fin τ.dim × ι → D)) := by
    apply mem_closure_iff_nhds.mpr
    intro W hW
    rw [nhds_pi] at hW
    obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hW
    obtain ⟨κ, hκ⟩ := exists_centralKernel_forall_mem μ
      (fun p : I => f p.val) (fun p : I => t p.val) (fun p => ht p.val)
    exact ⟨Φ κ, hsub fun p hp => hκ ⟨p, hp⟩, κ, rfl⟩
  rw [hclosed.closure_eq] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  have heq : (smoothingLM μ κ.val).comp j.toLinearMap = j.toLinearMap := by
    apply (LinearEquiv.piRing ℂ V (Fin τ.dim) ℂ).injective
    funext a i
    exact congrFun hκ (a, i)
  exact ⟨κ, fun v i => congrArg (fun T : (Fin τ.dim → ℂ) →ₗ[ℂ] V => T v i) heq⟩

end ContinuousSource

/-- One compact-central kernel reproduces every slice of every value of an algebraic
compact intertwiner whose image is killed by a fixed cofinite center ideal. -/
theorem exists_centralKernel_reproduces {m : ℕ}
    {σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)}
    (j : σ.IntertwiningMap ρ) (hJ : ∀ z ∈ J, ∀ v, (z : U) • j v = 0) :
    ∃ κ : compactCentralKernels F n, ∀ v i,
      CompactKernelAverage.smoothingLM μ κ.val (j v i) = j v i := by
  obtain ⟨τ, e, hr⟩ := exists_continuous_source j
  have hE (z : EnvelopingCenter F n) (hz : z ∈ J) (v : Fin τ.dim → ℂ) :
      (z : U) • e v = 0 := by
    have hv : e v ∈ j.toLinearMap.range := hr ▸ LinearMap.mem_range_self e.toLinearMap v
    obtain ⟨w, hw⟩ := hv
    change j w = e v at hw
    rw [← hw]
    exact hJ z hz w
  let : MeasurableSpace (standardInfiniteCompact F n) := borel _
  let : BorelSpace (standardInfiniteCompact F n) := ⟨rfl⟩
  let ν : Measure (standardInfiniteCompact F n) :=
    Measure.haarMeasure (⊤ : PositiveCompacts (standardInfiniteCompact F n))
  let : ν.IsHaarMeasure := by dsimp [ν]; infer_instance
  let : IsProbabilityMeasure ν := ⟨by
    change Measure.haarMeasure (⊤ : PositiveCompacts (standardInfiniteCompact F n)) Set.univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts (standardInfiniteCompact F n))))⟩
  obtain ⟨κ, hκ⟩ := exists_centralKernel_reproduces_of_continuous μ J ν τ e hE
  refine ⟨κ, fun v i => ?_⟩
  have hv : j v ∈ e.toLinearMap.range := hr.symm ▸ LinearMap.mem_range_self j.toLinearMap v
  obtain ⟨w, hw⟩ := hv
  change e w = j v at hw
  rw [← hw]
  exact hκ w i

end Langlands.Global.ArchimedeanGL.SmoothFamily
