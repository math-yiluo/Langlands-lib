# Rational points along a radicial map

Lean module: `Langlands.AlgebraicGeometry.LangWeil.CurvePlaneRadicialPoints`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

This module is a helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581).
Provenance: internal. It is the standard fact that a universal homeomorphism (here, an
injective map that is purely inseparable after a localization) induces a bijection on
rational points over a perfect field. No cited statement of the literature is formalized.

## Statement

`bijective_comp_of_radicial`: let `κ` be a field of exponential characteristic `p` that is a
perfect ring, `S` and `T` commutative `κ`-algebras, `j : S →ₐ[κ] T` an injective algebra map
and `s : S`. Suppose every `t : T` satisfies `j y = (j s ^ m * t) ^ p ^ n` for some
`m n : ℕ` and `y : S`. Then composition with `j` is a bijection from the `κ`-algebra maps
`ψ : T → κ` with `ψ (j s) ≠ 0` onto the `κ`-algebra maps `χ : S → κ` with `χ s ≠ 0`.

## Proof

*Injectivity.* If `ψ₁ ∘ j = ψ₂ ∘ j`, apply both to `y` with `j y = (j s ^ m * t) ^ p ^ n`.
This gives `(ψ₁(j s) ^ m ψ₁ t) ^ p ^ n = (ψ₁(j s) ^ m ψ₂ t) ^ p ^ n`. The `n`-th iterated
Frobenius of `κ` is injective (`iterateFrobeniusEquiv`), and `ψ₁ (j s) ≠ 0`, so
`ψ₁ t = ψ₂ t`.

*Surjectivity.* Given `χ` with `χ s ≠ 0`, pass to the localizations `S' = S[1/s]` and
`T' = T[1/j s]` with the induced map `j' = Localization.awayMap j s`. `χ` extends to
`χ' : S' → κ` (`IsLocalization.Away.lift`). The map `j'` is injective (from injectivity of
`j`) and `p`-radical (`IsPRadical`): a fraction `x = t / (j s) ^ k` satisfies
`x ^ p ^ n = j'(y · s^{-(m+k) p^n})`. Since `κ` is perfect, `PerfectRing.lift` extends
`χ'` along the `p`-radical `j'` to `ψ' : T' → κ`. Then `ψ = ψ' ∘ (T → T')` is a
`κ`-algebra map with `ψ ∘ j = χ` (`PerfectRing.lift_comp_apply`), and `ψ (j s) = χ s ≠ 0`.
