import Langlands.Representation.Compact.FiniteMean

/-! # Translation invariance of finite orbit means -/

namespace Langlands

open scoped BigOperators

universe uG uV

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Translating the initial vector does not change its orbit mean. -/
theorem Compact.orbitMean_apply (ρ : Representation ℂ G V) (g : G) (v : V) :
    Compact.orbitMean ρ (ρ g v) = Compact.orbitMean ρ v := by
  have horbit : Compact.orbit ρ (ρ g v) = Compact.orbit ρ v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * g, by simp⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h * g⁻¹, by simp⟩
  exact congrArg (fun S : Set V => (Nat.card S : ℂ)⁻¹ • ∑ᶠ x : S, x.val) horbit

end Langlands
