import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! Local units for actual smooth Hecke actions under the intended group hypotheses. -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact-open cofinality supplies an actual normalized local unit for each
smooth vector in a Hausdorff locally compact totally disconnected group. -/
theorem exists_normalizedIndicator_fixes (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (v : V) :
    ∃ (J : OpenSubgroup G) (hJ : IsCompact (J : Set G)),
      heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ J hJ) v = v := by
  obtain ⟨U, hU⟩ := hρ v
  obtain ⟨J, hJU, hJ, _⟩ :=
    TestFunction.commonCompactOpenBiInvariance G ∅ U
  refine ⟨J, hJ, heckeAction_normalizedIndicator_of_fixed μ ρ hρ J hJ ?_⟩
  exact fun j => hU ⟨j, hJU j.property⟩

/-- A single compact-open normalized indicator fixes any prescribed finite family
of smooth vectors. -/
theorem exists_normalizedIndicator_fixes_finset (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (s : Finset V) :
    ∃ (J : OpenSubgroup G) (hJ : IsCompact (J : Set G)),
      ∀ v ∈ s, heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ J hJ) v = v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨J, _, hJ, _⟩ :=
      TestFunction.commonCompactOpenBiInvariance G ∅ (⊤ : OpenSubgroup G)
    exact ⟨J, hJ, by simp⟩
  | @insert v s hv ih =>
    obtain ⟨J, hJ, hJs⟩ := ih
    obtain ⟨U, hU⟩ := hρ v
    obtain ⟨L, hLJU, hL, _⟩ :=
      TestFunction.commonCompactOpenBiInvariance G ∅ (J ⊓ U)
    refine ⟨L, hL, ?_⟩
    intro w hw
    apply heckeAction_normalizedIndicator_of_fixed μ ρ hρ L hL
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact fun l => hU ⟨l, (hLJU l.property).2⟩
    · have hfix : w ∈ fixedVectors ρ J.toSubgroup := by
        rw [← hJs w hw]
        exact heckeAction_normalizedIndicator_mem μ ρ hρ J hJ w
      exact fun l => hfix ⟨l, (hLJU l.property).1⟩

/-- The actual Hecke operators separate a smooth vector from zero. -/
theorem heckeAction_nondegenerate (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (v : V)
    (hv : ∀ f : HeckeAlgebra μ, heckeAction μ ρ hρ f v = 0) : v = 0 := by
  obtain ⟨J, hJ, h⟩ := exists_normalizedIndicator_fixes μ ρ hρ v
  rw [← h, hv]

end Langlands.Hecke
