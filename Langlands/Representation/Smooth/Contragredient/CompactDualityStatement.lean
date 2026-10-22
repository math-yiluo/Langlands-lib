import Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
import Mathlib.Basic.Complex.Basic

/-! # Compact-open fixed-vector duality for smooth complex representations -/

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Restriction identifies fixed smooth functionals with the full dual of the
fixed-vector space. The topological-group hypothesis is internal to the target. -/
def SmoothDualCompactFixedDualityStatement : Prop :=
  ∀ [IsTopologicalGroup G] (ρ : Representation ℂ G V),
    IsSmooth ρ → ∀ (K : OpenSubgroup G), IsCompact (K : Set G) →
      Function.Bijective (smoothDualFixedRestriction ρ K.toSubgroup)

end Langlands
