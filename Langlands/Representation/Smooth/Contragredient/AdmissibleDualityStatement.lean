import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Basic.Complex.Basic

/-! # Separation and reflexivity by smooth complex duals -/

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact-open cofinality gives separation by the smooth dual, preservation
of admissibility, and reflexivity of smooth admissible complex representations. -/
def SmoothAdmissibleDualityStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    (∀ (ρ : Representation ℂ G V) (hρ : IsSmooth ρ),
      Function.Injective (smoothBidual hρ)) ∧
    (∀ (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ),
      IsAdmissible (smoothContragredient ρ) ∧
        Function.Bijective (smoothBidual hρ.1))

end Langlands
