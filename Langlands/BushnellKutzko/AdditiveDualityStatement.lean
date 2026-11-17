import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.AdditiveDual

/-! # Additive duality for a hereditary order (Bushnell–Kutzko 1993, (1.1.4)–(1.1.6), p. 22) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u v

/-- **BK93 (1.1.4)–(1.1.6), printed p. 22.** Let `F` be a nonarchimedean local field, `V` an
`F`-vector space, `𝓛` an `𝔬_F`-lattice chain in `V` with `𝔄 = 𝔄(𝓛)` and `𝔓^n = End^n(𝓛)`.
Let `ψ_F` be an additive character of `F` that is trivial on `𝔭_F` but not on `𝔬_F`, and
`ψ_A = ψ_F ∘ tr_A`. Then
1. `(𝔓^n)^* = 𝔓^{1-n}` for all `n ∈ ℤ`;
2. for integers `n > r ≥ ⌊n/2⌋ ≥ 0`, the map `b ↦ ψ_b`, `ψ_b(g) = ψ_A(b(g - 1))`, induces an
   isomorphism from `𝔓^{-n}/𝔓^{-r}` onto the group of complex characters of
   `U^{r+1}(𝔄)/U^{n+1}(𝔄)`. This is stated as: (a) for `b ∈ 𝔓^{-n}`, `ψ_b` restricted to
   `U^{r+1}(𝔄)` is a character trivial on `U^{n+1}(𝔄)`; (b) for `b ∈ 𝔓^{-n}`, `ψ_b` is trivial
   on `U^{r+1}(𝔄)` if and only if `b ∈ 𝔓^{-r}`; (c) every character of `U^{r+1}(𝔄)` trivial on
   `U^{n+1}(𝔄)` is `ψ_b` for some `b ∈ 𝔓^{-n}`. (The map `b ↦ ψ_b` is additive because `ψ_A`
   is.) -/
def AdditiveDualityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type v) [AddCommGroup V] [Module F V] (𝓛 : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ), (∀ a ∈ 𝓂[F], ψF (a : F) = 1) → (∃ a : 𝒪[F], ψF (a : F) ≠ 1) →
    (∀ n : ℤ, additiveDual (traceCharacter ψF) (𝓛.endFiltration n : Set (Module.End F V)) =
      (𝓛.endFiltration (1 - n) : Set (Module.End F V))) ∧
    ∀ n r : ℕ, r < n → n / 2 ≤ r →
      (∀ b ∈ 𝓛.endFiltration (-(n : ℤ)),
        ∃ χ : 𝓛.unitFiltration (r + 1) →* ℂˣ,
          (∀ g : 𝓛.unitFiltration (r + 1),
            (χ g : ℂ) = elementCharacter (traceCharacter ψF) b g) ∧
          ∀ g : 𝓛.unitFiltration (r + 1),
            (g : (Module.End F V)ˣ) ∈ 𝓛.unitFiltration (n + 1) → χ g = 1) ∧
      (∀ b ∈ 𝓛.endFiltration (-(n : ℤ)),
        (∀ g ∈ 𝓛.unitFiltration (r + 1), elementCharacter (traceCharacter ψF) b g = 1) ↔
          b ∈ 𝓛.endFiltration (-(r : ℤ))) ∧
      ∀ χ : 𝓛.unitFiltration (r + 1) →* ℂˣ,
        (∀ g : 𝓛.unitFiltration (r + 1),
          (g : (Module.End F V)ˣ) ∈ 𝓛.unitFiltration (n + 1) → χ g = 1) →
        ∃ b ∈ 𝓛.endFiltration (-(n : ℤ)), ∀ g : 𝓛.unitFiltration (r + 1),
          (χ g : ℂ) = elementCharacter (traceCharacter ψF) b g

end Langlands.BushnellKutzko
