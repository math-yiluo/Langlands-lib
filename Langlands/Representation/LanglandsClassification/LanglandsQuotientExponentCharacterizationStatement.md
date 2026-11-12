# The Langlands quotient among the irreducible subquotients (Renard VII.4.2): statement

Module `Langlands.Representation.LanglandsClassification.LanglandsQuotientExponentCharacterizationStatement`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`.
The module contains one **statement**, the `Prop`-valued definition
`LanglandsQuotientExponentCharacterizationStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VII.4.2, the Theorem and the proof of (i), printed p.243 / PDF p.249.
After proving that `i_P^G(σ ⊗ ψ)` has a unique irreducible quotient, Renard writes:

> De plus, on voit d'après ce qui précède que `(π, V)` est caractérisé en tant que
> sous-quotient irréductible de `i_P^G(σ ⊗ ψ)` par la propriété
> `ℜ(ψ) ∈ ℜ(Exp(A_M, r_{P̄}^G(π)))`.

Here `(π, V) = J(P, σ, ψ)`, `P̄` is the parabolic opposite to `P`, `Exp(A_M, ·)` is the
set of normalized exponents along the split component `A_M` (VII.1.1), and `ℜ` is the
real part (V.3.20).

The published statement of the Theorem, `LanglandsClassificationStatement`, states
parts (i)–(iii). Its Markdown records this sentence as not stated. This unit states it.

## The statement

The setting and binders are those of the published `LanglandsQuotientUniqueStatement`:
`k` is a nonarchimedean local field, `G` is connected reductive, `(T, i, ν, D)` gives the
minimal parabolic and the reflection data, and `(P = MU, σ, ψ)` is a Langlands triplet
(`IsLanglandsTriplet`) with split component `a : A → M`. Further binders give a second
parabolic `P̄` with unipotent radical `Ū` and the same Levi `M`. They satisfy
`lbar ≫ pbar = l ≫ p` and `P(F) ∩ P̄(F) = M(F)` (`pointImage p ⊓ pointImage pbar =
pointImage (l ≫ p)`), as in the published VI.9.6 statements. These hypotheses say that
`P̄` is the opposite parabolic.

Write `I = i_P^G(σ ⊗ ψ)`, the published `leviInductionFunctor` applied to the twist of
`σ` by `ψ`. For every smooth representation `π` of `G(F)` on a carrier in the universe of
`I` that is irreducible and a subquotient of `I` (`SmoothRep.IsSubquotient π I`), the
statement asserts:

- `π` is an irreducible quotient of `I` (`Classification.IsIrreducibleQuotient`), if
  and only if
- some `χ ∈ normalizedJacquetExponents pbar lbar rbar … ha π` (the normalized exponents
  of `r_{P̄}^G(π)` along `A`) has normalized real part equal to `ℜ(ψ)`. The real parts
  are `Plancherel.SplitTorus.normalizedRealPart` for `χ` and the published
  `leviUnramifiedRealPart l hl a ha ψ` for `ψ`.

## Formalization choices

- **"Characterized".** By part (i), the irreducible quotients of `I` are the
  representations isomorphic to `J(P, σ, ψ)`. So "`π ≅ J(P, σ, ψ)`" is stated as "`π` is
  an irreducible quotient of `I`". This needs no chosen Langlands quotient.
- **`ℜ(ψ) ∈ ℜ(Exp(A_M, ·))`** is the existence of an exponent `χ` with
  `ℜ(χ) = ℜ(ψ)`. Both real parts are taken in the real character space of `A` with the
  same normalized convention, the one used by `IsLanglandsTriplet`.
- **Opposite parabolic.** As in the published VI.9.6 statements, `P̄` is any parabolic
  with Levi `M` such that `P(F) ∩ P̄(F) = M(F)`. These are the parabolics opposite to
  `P` with respect to `M`.
- **Universes.** `π` lives in the universe `max u v` of `I`, as in the published
  statement of part (i).

## Why the statement is true

The proof is a separate obligation. Renard's argument: by second adjointness (VI.9.6),
`Hom_G(I, π) ≅ Hom_M(σ ⊗ ψ, r_{P̄}^G(π))`. So the Langlands quotient contains `σ ⊗ ψ`
in `r_{P̄}^G`. Its central exponent along `A_M` has real part `ℜ(ψ)`, because `σ` is
tempered and therefore has a unitary central character on `A_M` (VII.2.1, Remark 1).
Conversely, by the geometric lemma (VI.5.1) and the `PP̄`-regularity of `σ ⊗ ψ` (VII.4.1,
Lemma), the exponents of `r_{P̄}^G(I)` with real part `ℜ(ψ)` come only from the piece
`σ ⊗ ψ`, which occurs once. Since `r_{P̄}^G` is exact, exactly one composition factor of
`I` has such an exponent, and it is the Langlands quotient.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement` | `IsLanglandsTriplet`, `leviUnramifiedCharacters`, `leviUnramifiedRealPart`, `leviInductionFunctor`, `Classification.IsIrreducibleQuotient` (through its imports) |
| `Langlands.Representation.Exponents.ArbitraryParabolic` | `normalizedJacquetExponents`, `pointImage` |
| `Langlands.Representation.Category.Subquotients` | `SmoothRep.IsSubquotient` |
