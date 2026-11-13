import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs

/-! # Ogoma's lemma on annihilators after localization -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.10.1 (07FC, Ogoma): let `A` be Noetherian, `M` a finite `A`-module, `S ⊆ A`
multiplicative and `π ∈ A` with `Ker(π : S⁻¹M → S⁻¹M) = Ker(π² : S⁻¹M → S⁻¹M)`. Then there is
`s ∈ S` with `Ker(tsπ : M → M) = Ker((tsπ)² : M → M)` for every `t ∈ S` (Stacks states this for
`t = sⁿ⁻¹`; its proof gives every `t ∈ S`). The kernel equalities are written as implications,
the reverse inclusions being automatic; an element of `S⁻¹M` is killed by `π` or `π²` exactly
when some `s ∈ S` times `π • m` or `π² • m` vanishes in `M`. -/
def AnnihilatorStabilizationStatement : Prop :=
  ∀ (A M : Type u) [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (S : Submonoid A) (π : A),
    (∀ m : M, (∃ s ∈ S, (s * π ^ 2) • m = 0) → ∃ s ∈ S, (s * π) • m = 0) →
    ∃ s ∈ S, ∀ t ∈ S, ∀ m : M, (t * s * π) ^ 2 • m = 0 → (t * s * π) • m = 0

end Langlands.CommutativeAlgebra.Popescu
