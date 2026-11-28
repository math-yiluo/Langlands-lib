import Langlands.Correspondence.Laumon.SlopeCalculus
import Langlands.LocalField.LaurentSeries

/-!
# The Artin–Schreier line `Lψ(c/t)` has slope one

Laumon 1987, Exemple (2.1.2.8), p. 154: over a henselian trait of equal characteristic `p` with
uniformizer `π`, the Artin–Schreier covering `(1/π')^p − (1/π') = 1/π` is Galois with group
`𝔽_p`, and the character `ψ⁻¹` of this group, for Laumon's nontrivial additive character
`ψ : 𝔽_p → ℚ̄_ℓ^×`, defines a Galois module `Lψ(1/π)` of rank one and Swan conductor one
(Serre, *Local Fields*, IV §2, Exercise 5).

This module works over the completed end trait `X = k((t))` (`LaurentSeries k`, `k` finite) with
separable closure `Ω = SeparableClosure X`, and with a nontrivial additive character
`ψ : k₀ → E` of a finite field `k₀ ⊆ k` with `q` elements, the field of the Fourier character.
For `c ∈ k` the Artin–Schreier–Lang equation `u^q − u = c/t` has a root `u ∈ Ω`; every
`σ ∈ Gal(Ω/X)` moves it by a translation `σ u = u + a_σ` with `a_σ ∈ k₀`, and the character of
`Lψ(c/t)` is `σ ↦ ψ(−a_σ)`, Laumon's `ψ⁻¹` convention. Laumon's example is the case of the prime
field `k₀ = 𝔽_p` and `c = 1`, with `π = t`; the residue field `k` may be any finite field
containing `𝔽_p`. For a general `k₀` with `q` elements the equation is the degree-`q` Lang
construction for the additive group over `k₀` (Laumon (1.1.3)): for `c ≠ 0` its splitting field
over `X` has degree `q` and Galois group `k₀`, acting by translations, while for `c = 0` the
polynomial splits over `X` and the character is trivial.

The root and the translation are chosen by `Classical.epsilon`; that the values form a
continuous character is part of `ArtinSchreierPoleOneStatement`.
-/

noncomputable section

universe u v

open Langlands.Henniart.LocalNumerical (IsLadicContinuous IsLadicDefinedOverFiniteExtension)

namespace Langlands.Henniart.Laumon

section ArtinSchreier

variable (k₀ : Type u) [Field k₀] (k : Type v) [Field k] [Algebra k₀ k]

/-- A root `u` in the separable closure of `k((t))` of the Artin–Schreier–Lang equation
`u^q − u = c/t`, where `q` is the cardinality of `k₀` and `c/t` is the Laurent series
`HahnSeries.single (-1) c`. -/
def artinSchreierRoot (c : k) : SeparableClosure (LaurentSeries k) :=
  Classical.epsilon fun u : SeparableClosure (LaurentSeries k) =>
    u ^ Nat.card k₀ - u =
      algebraMap (LaurentSeries k) (SeparableClosure (LaurentSeries k)) (HahnSeries.single (-1) c)

/-- The translation `a_σ ∈ k₀` with `σ u = u + a_σ` for the root `u = artinSchreierRoot k₀ k c`. -/
def artinSchreierTranslation (c : k)
    (σ : SeparableClosure (LaurentSeries k) ≃ₐ[LaurentSeries k]
      SeparableClosure (LaurentSeries k)) : k₀ :=
  Classical.epsilon fun a : k₀ =>
    σ (artinSchreierRoot k₀ k c) = artinSchreierRoot k₀ k c +
      algebraMap (LaurentSeries k) (SeparableClosure (LaurentSeries k))
        (HahnSeries.C (algebraMap k₀ k a))

/-- The value `ψ(−a_σ)` at `σ` of the character of `Lψ(c/t)`. -/
def artinSchreierValue {ℓ : ℕ} [Fact ℓ.Prime] (ψ : AddChar k₀ (PadicAlgCl ℓ)) (c : k)
    (σ : SeparableClosure (LaurentSeries k) ≃ₐ[LaurentSeries k]
      SeparableClosure (LaurentSeries k)) : PadicAlgCl ℓ :=
  ψ (-artinSchreierTranslation k₀ k c σ)

end ArtinSchreier

/-- Laumon (2.1.2.8) for the degree-`q` equation `u^q − u = c/t` (Laumon's example is
`k₀ = 𝔽_p`, `c = 1`): for finite fields `k₀ ⊆ k`, a nontrivial additive character
`ψ : k₀ → E` and `X = k((t))`,

* for every `c ∈ k` the values `artinSchreierValue k₀ k ψ c` are those of a continuous character
  `χ_c` of `Gal(Ω/X)` with values in a finite extension of `ℚ_ℓ`;
* for `c ≠ 0` the line `Lψ(c/t)` of `χ_c` has the single slope `1`, so Swan conductor `1`;
* for `c ≠ c'` the ratio `χ_c χ_{c'}⁻¹` of the two Artin–Schreier kernels with linear
  parameters `c` and `c'` again has the single slope `1` and Swan conductor `1`. -/
def ArtinSchreierPoleOneStatement.{u₀, u₁} : Prop :=
  ∀ (k₀ : Type u₀) [Field k₀] [Finite k₀] (k : Type u₁) [Field k] [Finite k] [Algebra k₀ k]
    (ℓ : ℕ) [Fact ℓ.Prime] (ψ : AddChar k₀ (PadicAlgCl ℓ)), ψ ≠ 1 →
    letI : ValuativeRel (LaurentSeries k) := LocalField.Laurent.valuativeRel k
    (∀ c : k, ∃ χ : (SeparableClosure (LaurentSeries k) ≃ₐ[LaurentSeries k]
          SeparableClosure (LaurentSeries k)) →* (PadicAlgCl ℓ)ˣ,
        (∀ σ, (χ σ : PadicAlgCl ℓ) = artinSchreierValue k₀ k ψ c σ) ∧
        IsLadicContinuous ℓ (ladicCharacterLine χ) ∧
        IsLadicDefinedOverFiniteExtension ℓ (ladicCharacterLine χ)) ∧
    (∀ c : k, c ≠ 0 →
      ∀ χ : (SeparableClosure (LaurentSeries k) ≃ₐ[LaurentSeries k]
          SeparableClosure (LaurentSeries k)) →* (PadicAlgCl ℓ)ˣ,
        (∀ σ, (χ σ : PadicAlgCl ℓ) = artinSchreierValue k₀ k ψ c σ) →
          slopeSupport (MonoidHom.id _) (ladicCharacterLine χ) = {1} ∧
          ladicSwan (MonoidHom.id _) (ladicCharacterLine χ) = 1) ∧
    (∀ c c' : k, c ≠ c' →
      ∀ χ χ' : (SeparableClosure (LaurentSeries k) ≃ₐ[LaurentSeries k]
          SeparableClosure (LaurentSeries k)) →* (PadicAlgCl ℓ)ˣ,
        (∀ σ, (χ σ : PadicAlgCl ℓ) = artinSchreierValue k₀ k ψ c σ) →
        (∀ σ, (χ' σ : PadicAlgCl ℓ) = artinSchreierValue k₀ k ψ c' σ) →
          slopeSupport (MonoidHom.id _) (ladicCharacterLine (χ * χ'⁻¹)) = {1} ∧
          ladicSwan (MonoidHom.id _) (ladicCharacterLine (χ * χ'⁻¹)) = 1)

end Langlands.Henniart.Laumon
