import Langlands.Representation.Archimedean.RealGenericLargeReduction

/-!
# One-sided nonvanishing for Harish-Chandra bimodules of `𝔤𝔩_n(ℂ)`

An algebraic form of the one-sided nonvanishing `V ≠ 𝔫^{(0)} V` of the Jacquet module of an
irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module, phrased for two commuting actions `ℓ`, `r` of
`𝔤𝔩_n(ℂ)` on `V` (the two factors of `𝔤𝔩_n(ℂ) ⊗_ℝ ℂ ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`).
See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

/-- One-sided nonvanishing for Harish-Chandra bimodules of `𝔤𝔩_n(ℂ)` (Bernstein–Gelfand 1980,
Theorem 5.9): let `ℓ`, `r` be commuting actions of `𝔤𝔩_n(ℂ)` on `V` and `E ⊆ V` a nonzero
finite-dimensional subspace, stable under `κ(Y) = ℓ(Y) - r(Yᵀ)` for all `Y`, spanned by vectors on
which every `κ(E_pp)` acts by an integer, and generating `V` under `ℓ`. If the center of
`U(𝔤𝔩_n(ℂ))` acts by scalars through `ℓ`, then the strictly upper triangular matrix units do
not span `V` under `ℓ`: `ℓ(𝔫) V ≠ V`. -/
def ComplexJacquetBimoduleStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ℓ r : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V),
    (∀ X Y, ℓ X * r Y = r Y * ℓ X) →
    ∀ E : Submodule ℂ V, FiniteDimensional ℂ E → E ≠ ⊥ →
      (∀ Y : Matrix (Fin n) (Fin n) ℂ, ∀ e ∈ E, ℓ Y e - r Y.transpose e ∈ E) →
      E ≤ Submodule.span ℂ {e | e ∈ E ∧ ∃ m : Fin n → ℤ, ∀ p : Fin n,
        ℓ (Matrix.single p p 1) e - r (Matrix.single p p 1) e = (m p : ℂ) • e} →
      (∀ S : Submodule ℂ V, E ≤ S → (∀ X, ∀ s ∈ S, ℓ X s ∈ S) → S = ⊤) →
      HasInfinitesimalCharacter ℓ →
      Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), p < q ∧ ℓ (Matrix.single p q 1) v = w}
        ≠ ⊤

end Langlands.Archimedean
