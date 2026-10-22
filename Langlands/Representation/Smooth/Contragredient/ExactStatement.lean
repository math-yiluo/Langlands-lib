import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Algebra.Exact.Basic
import Mathlib.Basic.Complex.Basic

/-! # Short exact sequences and the smooth contragredient -/

namespace Langlands

universe uG uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- Smooth complex contragredients reverse short exact sequences when compact
open subgroups are cofinal among open subgroups. -/
def SmoothContragredientShortExactStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K) →
    ∀ (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
      (τ : Representation ℂ G X), IsSmooth ρ → IsSmooth σ →
    ∀ (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
        Function.Injective (contragredientMap g) ∧
        Function.Exact (contragredientMap g) (contragredientMap f) ∧
        Function.Surjective (contragredientMap f)

end Langlands
