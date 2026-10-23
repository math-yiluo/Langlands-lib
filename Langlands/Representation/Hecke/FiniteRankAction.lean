import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Factor the actual integrated action through fixed vectors, and deduce finite
rank from admissibility. No topology on the representation carrier is used.
-/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The full integrated operator, with codomain restricted to the actual
fixed vectors under a subgroup of left invariance. -/
def integratedActionToFixed {K J : Subgroup G} {f : SchwartzBruhat G}
    (hf : f ∈ TestFunction.biInvariant K J) :
    V →ₗ[ℂ] fixedVectors ρ K :=
  (integratedAction μ ρ hρ f).codRestrict (fixedVectors ρ K)
    (integratedAction_mem_fixedVectors μ ρ hρ hf)

@[simp]
theorem integratedActionToFixed_apply {K J : Subgroup G} {f : SchwartzBruhat G}
    (hf : f ∈ TestFunction.biInvariant K J) (v : V) :
    (integratedActionToFixed μ ρ hρ hf v : V) =
      integratedAction μ ρ hρ f v := rfl

/-- The restricted-codomain map is a factorization of the actual operator. -/
theorem subtype_comp_integratedActionToFixed {K J : Subgroup G}
    {f : SchwartzBruhat G} (hf : f ∈ TestFunction.biInvariant K J) :
    (fixedVectors ρ K).subtype.comp (integratedActionToFixed μ ρ hρ hf) =
      integratedAction μ ρ hρ f := rfl

/-- Left bi-invariance controls the whole image, independently of admissibility. -/
theorem integratedAction_range_le_fixedVectors {K J : Subgroup G}
    {f : SchwartzBruhat G} (hf : f ∈ TestFunction.biInvariant K J) :
    LinearMap.range (integratedAction μ ρ hρ f) ≤ fixedVectors ρ K := by
  rintro _ ⟨v, rfl⟩
  exact integratedAction_mem_fixedVectors μ ρ hρ hf v

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Finitely many actual Hecke operators have images in one finite-dimensional
fixed-vector space, with its compact open subgroup inside any prescribed open
subgroup. -/
theorem exists_common_finiteDimensional_fixedVectors
    (hρa : IsAdmissible ρ) (s : Finset (SchwartzBruhat G)) (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧
      FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) ∧
      ∀ f ∈ s, LinearMap.range (integratedAction μ ρ hρa.1 f) ≤
        fixedVectors ρ K.toSubgroup := by
  obtain ⟨K, hKU, hK, hs⟩ := TestFunction.commonCompactOpenBiInvariance G s U
  exact ⟨K, hKU, hK, hρa.2 K, fun f hf =>
    integratedAction_range_le_fixedVectors μ ρ hρa.1 (hs f hf)⟩

/-- Admissibility makes every actual integrated test-function operator finite
rank even when the representation space is infinite-dimensional. -/
theorem integratedAction_finiteDimensional_range (hρa : IsAdmissible ρ)
    (f : SchwartzBruhat G) :
    FiniteDimensional ℂ (LinearMap.range (integratedAction μ ρ hρa.1 f)) := by
  classical
  obtain ⟨K, _, _, hKfinite, hKrange⟩ :=
    exists_common_finiteDimensional_fixedVectors μ ρ hρa {f} ⊤
  let := hKfinite
  exact Submodule.finiteDimensional_of_le (hKrange f (Finset.mem_singleton_self f))

/-- The measure-indexed Hecke algebra action has the same finite-rank property. -/
theorem heckeAction_finiteDimensional_range (hρa : IsAdmissible ρ)
    (f : HeckeAlgebra μ) :
    FiniteDimensional ℂ (LinearMap.range (heckeAction μ ρ hρa.1 f)) :=
  integratedAction_finiteDimensional_range μ ρ hρa
    (HeckeAlgebra.toTestFunction μ f)

end Langlands.Hecke
