import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Basic.Complex.Basic

/-! # Linear duality of intertwiner spaces -/

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Smooth contragredient pullback identifies the intertwiner spaces when the
source is smooth, the target is admissible, and compact opens are cofinal. -/
def SmoothContragredientHomDualityStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (ρ : Representation ℂ G V) (σ : Representation ℂ G W),
      IsSmooth ρ → IsAdmissible σ →
      ∃ e : ρ.IntertwiningMap σ ≃ₗ[ℂ]
        (smoothContragredient σ).IntertwiningMap (smoothContragredient ρ),
        ∀ f, e f = contragredientMap f

end Langlands
