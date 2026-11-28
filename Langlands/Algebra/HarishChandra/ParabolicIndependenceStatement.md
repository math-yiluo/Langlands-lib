# Independence of the parabolic for the normalized Levi component: statement

Module `Langlands.Algebra.HarishChandra.ParabolicIndependenceStatement`, namespace
`Langlands.Algebra.HarishChandra`. The module contains definitions and one statement.
It proves nothing beyond the well-formedness of the definitions.

## Definitions

Let `𝔤` be a complex Lie algebra (`L`) and `H` a Lie subalgebra. `𝔤` is a Lie module over `H`
by restriction of the adjoint action. For a function `χ : H → ℂ`, `weightSpace L χ` is Mathlib's
weight space `{x | ∀ h, [h, x] = χ(h) x}`.

- `IsSplitCartan H` bundles six conditions on `H`:
  1. `H` is abelian (`isLieAbelian`).
  2. The weight spaces of `H` span `𝔤` (`iSup_weightSpace_eq_top`). So `ad H` is
     diagonalizable.
  3. The zero weight space is `H` itself (`weightSpace_zero`).
  4. Every weight space `𝔤_χ ≠ 0` with `χ ≠ 0` (a root space) has dimension one
     (`finrank_weightSpace`).
  5. For every root `χ` there are `e ∈ 𝔤_χ`, `f ∈ 𝔤_{-χ}` and `h ∈ H` with `[e, f] = h` and
     `χ(h) = 2` (`exists_sl2`).
  6. If `χ` and `c • χ` are roots with `c ≠ 0`, then `c = ±1` (`reduced`).

  For a complex semisimple Lie algebra these properties of a Cartan subalgebra are proved in
  Humphreys, *Introduction to Lie Algebras and Representation Theory* (GTM 9): see §8.3,
  Proposition (f) (the triples), and §8.4, Proposition (a) and (b) (lines, and the multiples
  `±α`), printed pp. 38–39 (PDF pp. 51–52). A complex reductive Lie algebra is the sum of its
  centre and its semisimple derived algebra, so a Cartan subalgebra of it has the same
  properties. Knapp–Vogan, *Cohomological Induction and Unitary Representations* (1995),
  Chapter IV §8 works with this root decomposition for Lemma 4.123 and Proposition 4.129.
- `positiveEigenSubmodule X` is the sum over the integers `n > 0` of the eigenspaces of `ad X`
  for the eigenvalue `n`. If `X ∈ H` takes integer values on all roots, this is the sum of the
  root spaces `𝔤_χ` with `χ(X) > 0`. It is the nilradical `𝔳` of the parabolic subalgebra
  attached to `X`, whose Levi factor is the centralizer `ker ad X`.
- `generatorRightIdeal V` is the complex span of the products `ι(x) · b` with `x ∈ V` and
  `b ∈ U(𝔤)`. This is the right ideal `V · U(𝔤)` of the universal enveloping algebra.
- `scalarShiftLie lam hlam` is the Lie algebra map `Y ↦ ι(Y) + λ(Y) · 1` from a complex Lie
  algebra `𝔪` into `U(𝔪)`. Here `λ` is a linear form that vanishes on brackets (`hlam`).
  `scalarShift lam hlam` is the induced algebra endomorphism of `U(𝔪)`.
  It is an automorphism, with inverse the shift by `-λ`.

## Statement `ParabolicIndependenceStatement`

The statement quantifies over a finite-dimensional complex Lie algebra `𝔤` with a subalgebra
`H` satisfying `IsSplitCartan H`, and over a complex Lie algebra `𝔪` with a Lie algebra map
`ι : 𝔪 → 𝔤` and elements `X₁, X₂ ∈ H`. It assumes:

- on every weight `χ` of `H` (every `χ` with `𝔤_χ ≠ 0`), `χ(X₁)` and `χ(X₂)` are integers,
  and `χ(X₁) = 0` exactly when `χ(X₂) = 0`;
- `ι` is injective with range the centralizer `ker ad X₁` (equal to `ker ad X₂` by the previous
  hypothesis);
- `λ₁` and `λ₂` are linear forms on `𝔪` vanishing on brackets with
  `2 λᵢ(Y) = tr(ad ι(Y) | 𝔳ᵢ)` for every `Y ∈ 𝔪`, where `𝔳ᵢ = positiveEigenSubmodule Xᵢ`.
  The trace is taken of the restriction of `ad ι(Y)` to `𝔳ᵢ`. The hypothesis is stated for every
  proof that `ad ι(Y)` maps `𝔳ᵢ` into itself. Such a proof exists because `ι(Y)` commutes with
  `Xᵢ`.

The conclusion is the following. Let `z` be central in `U(𝔤)` and let `y₁, y₂ ∈ U(𝔪)` satisfy
`z - j(yᵢ) ∈ 𝔳ᵢ · U(𝔤)` for `i = 1, 2`, where `j : U(𝔪) → U(𝔤)` is induced by `ι`. Then
`τ_{λ₁}(y₁) = τ_{λ₂}(y₂)`, where `τ_λ = scalarShift λ`.

So `λᵢ = ρ(𝔳ᵢ)` is half the sum of the roots in `𝔳ᵢ`, as a linear form on the Levi factor.
The statement says that the component `y` of `z` in `U(𝔪)` modulo `𝔳 · U(𝔤)`, shifted by
`Y ↦ Y + ρ(𝔳)(Y)`, does not depend on the parabolic subalgebra `𝔪 ⊕ 𝔳` with Levi factor `𝔪`.

## Source and conventions

This is Knapp–Vogan (1995), Proposition 4.129 (c), printed p. 303 (PDF p. 325), with the maps
of Lemma 4.123 (printed p. 301) and (4.124)–(4.128) (printed pp. 302–303). There `μ_{𝔤/𝔩}` is the
projection to `U(𝔩)` along `𝔲̄ U(𝔤) + U(𝔤) 𝔲`, and `τ_𝔲(X) = X - δ(𝔲)(X)` with `δ(𝔲)` half the
sum of the roots in `𝔲`. Part (c) identifies `μ̃_{𝔤/𝔩} = τ_𝔲 ∘ μ_{𝔤/𝔩}` on the centre with
`γ_𝔩⁻¹ ∘ γ`, where `γ` and `γ_𝔩` are the Harish-Chandra isomorphisms of `𝔤` and `𝔩`. That
expression does not involve `𝔲` (the remark after (4.128)).

The statement here mirrors this to right ideals. The principal anti-automorphism of `U(𝔤)`
(`X ↦ -X` on `𝔤`) carries `U(𝔤) 𝔳` to `𝔳 U(𝔤)` and fixes the centre setwise. It turns the
shift `X ↦ X - ρ(𝔳)(X)` into `X ↦ X + ρ(𝔳)(X)`. For `𝔰𝔩₂ = ⟨e, h, f⟩` with `X₁ = h`, `X₂ = -h`
and the Casimir element `z = h²/2 + ef + fe`, the components are `h²/2 - h` (modulo `e U`) and
`h²/2 + h` (modulo `f U`). The shifts by `±1` on `h` give `h²/2 - 1/2` in both cases.

`scalarShift_ι` evaluates the scalar shift on a Lie generator.
