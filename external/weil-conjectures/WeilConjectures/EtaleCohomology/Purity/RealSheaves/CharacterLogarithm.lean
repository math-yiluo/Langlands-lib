/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic
public import WeilConjectures.NumberTheory.Padics.Exponential

/-!
# The logarithm of a character of the Weil group

Let `χ : W(C₀) → Eˣ` be a character of the Weil group of a curve over a finite field with values
in a finite extension `E / ℚ_ℓ`, continuous on the geometric fundamental group `π₁(C) = ker deg`.
Since `π₁(C)` is compact, some power `χ ^ N` maps `π₁(C)` into the principal units
`1 + ℓ² 𝒪_E`, and `λ(g) = log (χ(g) ^ N)` is a continuous additive character of `π₁(C)` that is
invariant under conjugation by any element of `W(C₀)`, in particular by a degree-one element
(blueprint `theorem-rank-one-sheaves-have-finite`).

## Main statements

- `AlgebraicGeometry.WeilGroup.exists_smallLog_pow_hom`: the logarithm of a power of `χ`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable (W : WeilGroup p) {l : ℕ} [Fact l.Prime] {E : Type*} [Field E]
  [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- Blueprint `theorem-rank-one-sheaves-have-finite`: A multiplicative curve character produces an
invariant additive character.

Let `χ : W(C₀) → Eˣ` be a character with values in a finite extension `E / ℚ_ℓ` inside `ℚ̄_ℓ`,
continuous on `Π = π₁(C) = ker deg`, and let `s ∈ W(C₀)` (for instance of degree one). There is
`N ≥ 1` such that `χ(g) ^ N` lies in the principal units `1 + ℓ² 𝒪_E` (on which the logarithm is
defined) for `g ∈ Π`, and `λ(g) = log (χ(g) ^ N)` is a continuous additive character of `Π`
with `λ(s g s⁻¹) = λ(g) = λ(s⁻¹ g s)`. The compactness of `Π` is the field
`AlgebraicGeometry.WeilGroup.compactSpace_ker`; the invariance holds because the values of `χ`
commute. -/
theorem exists_smallLog_pow_hom (χ : W.carrier →* Eˣ)
    (hχ : Continuous fun g : W.geometric ↦ algebraMap E (PadicAlgCl l) (χ g)) (s : W.carrier) :
    ∃ N : ℕ, 0 < N ∧ (∀ g : W.geometric, χ g ^ N ∈ PadicAlgCl.smallUnits l E) ∧
      (∀ g h : W.geometric, PadicAlgCl.smallLog l E ((χ (g * h) : E) ^ N - 1) =
        PadicAlgCl.smallLog l E ((χ g : E) ^ N - 1) +
          PadicAlgCl.smallLog l E ((χ h : E) ^ N - 1)) ∧
      (Continuous fun g : W.geometric ↦
        algebraMap E (PadicAlgCl l) (PadicAlgCl.smallLog l E ((χ g : E) ^ N - 1))) ∧
      (∀ g h : W.geometric, (h : W.carrier) = s * g * s⁻¹ →
        PadicAlgCl.smallLog l E ((χ h : E) ^ N - 1) =
          PadicAlgCl.smallLog l E ((χ g : E) ^ N - 1)) ∧
      (∀ g h : W.geometric, (h : W.carrier) = s⁻¹ * g * s →
        PadicAlgCl.smallLog l E ((χ h : E) ^ N - 1) =
          PadicAlgCl.smallLog l E ((χ g : E) ^ N - 1)) := by
  obtain ⟨N, hN, hsmall, hmul, hcont⟩ :=
    PadicAlgCl.exists_smallLog_pow_hom (χ.comp W.geometric.subtype) hχ
  have hconj (g h : W.geometric) (t : W.carrier) (hgh : (h : W.carrier) = t * g * t⁻¹) :
      χ h = χ g := by
    rw [hgh, map_mul, map_mul, mul_comm (χ t), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
  refine ⟨N, hN, hsmall, hmul, hcont, fun g h hgh ↦ ?_, fun g h hgh ↦ ?_⟩
  · rw [hconj g h s hgh]
  · rw [hconj g h s⁻¹ (by rw [inv_inv, hgh])]

end WeilGroup

end AlgebraicGeometry
