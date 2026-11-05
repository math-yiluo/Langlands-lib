import Langlands.Representation.Category.Contragredient

/-! # Finite-length uniformization of coefficient growth -/

noncomputable section

namespace Langlands.Plancherel

universe uG uV

/-- The algebraic finite-length step in moderate coefficient growth.
The coefficientwise estimate remains a premise of this internal target. -/
def FiniteLengthCoefficientGrowthUniformizationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    CompactOpenCofinal G →
    ∀ (H : G → ℝ), (∀ g, 1 ≤ H g) →
      (∀ g h, H (g * h) ≤ H g * H h) →
      ∀ (π : SmoothRep.{0, uG, uV} ℂ G),
        π.IsAdmissible → π.HasFiniteLength →
        (∀ (v : π) (φ : SmoothDual π.representation),
          ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : G,
            ‖(φ : Module.Dual ℂ π) (π.representation g v)‖ ≤ c * H g ^ d) →
        ∃ d : ℕ, ∀ (v : π) (φ : SmoothDual π.representation),
          ∃ c : ℝ, 0 < c ∧ ∀ g : G,
            ‖(φ : Module.Dual ℂ π) (π.representation g v)‖ ≤ c * H g ^ d

end Langlands.Plancherel
