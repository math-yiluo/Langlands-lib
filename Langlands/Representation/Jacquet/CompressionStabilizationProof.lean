import Langlands.Representation.Jacquet.CompressionStabilizationStatement
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Fitting stabilization of compact compressed actions

The actual compressed action on a finite-dimensional fixed-vector module has
stationary power ranges and kernels, a Fitting decomposition, and a bijective
restriction to its stable image.
-/

namespace Langlands.Jacquet

universe uG uV

/-- Finite-dimensional Fitting theory applied to the published compact
compression, with all group and representation data quantified internally. -/
theorem compactCompression_stabilization :
    CompactCompressionStabilizationStatement.{uG, uV} := by
  intro G _ _ _ V _ _ ρ hρ K hK g hfin
  let C := compressedAction ρ hρ K hK g
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp
    (C.eventually_iInf_range_pow_eq.and C.eventually_iSup_ker_pow_eq)
  have hSplit : CompactCompressionSplits ρ hρ K hK g :=
    LinearMap.isCompl_iSup_ker_pow_iInf_range_pow C
  refine ⟨⟨r, fun s hs => ⟨(hr s hs).1, (hr s hs).2⟩⟩, hSplit, ?_⟩
  have hinj : Function.Injective (stableImageAction ρ hρ K hK g) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv0 : C (v : fixedVectors ρ K.toSubgroup) = 0 := by
      have := congrArg Subtype.val hv
      simpa [stableImageAction_apply] using this
    have hker : (v : fixedVectors ρ K.toSubgroup) ∈ powerKernelSup ρ hρ K hK g := by
      refine Submodule.mem_iSup_of_mem 1 ?_
      simpa [LinearMap.mem_ker] using hv0
    have := hSplit.disjoint.le_bot ⟨hker, v.property⟩
    exact Subtype.ext (by simpa using this)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

section Consequences

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- One threshold simultaneously stabilizes all power ranges and kernels. -/
theorem compactCompression_eventuallyStable (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    CompactCompressionEventuallyStable ρ hρ K hK g :=
  (compactCompression_stabilization ρ hρ K hK g hfin).1

/-- The actual power-kernel supremum and stable image are complementary. -/
theorem powerKernelSup_isCompl_stableImage (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    IsCompl (powerKernelSup ρ hρ K hK g) (stableImage ρ hρ K hK g) :=
  (compactCompression_stabilization ρ hρ K hK g hfin).2.1

/-- The existing restriction of compression to its stable image is bijective. -/
theorem stableImageAction_bijective (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    Function.Bijective (stableImageAction ρ hρ K hK g) :=
  (compactCompression_stabilization ρ hρ K hK g hfin).2.2

/-- Admissibility supplies smoothness and finite dimensionality of the actual
fixed-vector module; compactness is still supplied by `hK`. -/
theorem compactCompression_stabilizes_of_isAdmissible
    (ρ : Representation ℂ G V) (hAdm : IsAdmissible ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) :
    CompactCompressionStabilizes ρ hAdm.1 K hK g :=
  compactCompression_stabilization ρ hAdm.1 K hK g (hAdm.2 K)

end Consequences

end Langlands.Jacquet
