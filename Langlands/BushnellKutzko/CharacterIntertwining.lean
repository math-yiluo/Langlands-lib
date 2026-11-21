import Mathlib

/-! # Intertwining of characters (Bushnell–Kutzko 1993, §3.3, printed p. 104) -/

namespace Langlands.BushnellKutzko

universe u

variable {G : Type u} [Group G]

/-- The elements `g` for which `χ₁(g h g⁻¹) = χ₂(h)` on `g⁻¹ H₁ g ∩ H₂`. -/
def characterIntertwining {H₁ H₂ : Subgroup G} (χ₁ : H₁ →* ℂˣ) (χ₂ : H₂ →* ℂˣ) : Set G :=
  {g | ∀ (h : H₂) (hh : g * (h : G) * g⁻¹ ∈ H₁), χ₁ ⟨_, hh⟩ = χ₂ h}

/-- The self-intertwining set `I_G(χ)`. -/
abbrev characterSelfIntertwining {H : Subgroup G} (χ : H →* ℂˣ) : Set G :=
  characterIntertwining χ χ

/-- The `G`-normalizer of a character consists of the normalizers of its domain
that also intertwine the character with itself. -/
def characterNormalizer {H : Subgroup G} (χ : H →* ℂˣ) : Set G :=
  (Subgroup.normalizer (H : Set G) : Set G) ∩ characterSelfIntertwining χ

end Langlands.BushnellKutzko
