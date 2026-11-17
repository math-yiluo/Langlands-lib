# Degrees of endomorphisms along lines are polynomial

`Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. The statement quantifies over:

- every algebraically closed field `k : Type u` (of any characteristic);
- every abelian scheme `A` over `Spec k`;
- every natural number `g` with `A.HasRelativeDimension g`.

It asserts that there is a function `δ : (A ⟶ A) → ℚ` on the actual endomorphisms of `A` with two properties.

1. On isogenies `δ` is the degree: if `IsIsogeny β`, then `δ β = (hom β).finrank y` (cast to `ℚ`) at every point `y` of the scheme `A.X.left`.
2. `δ` is polynomial of degree at most `2 * g` along every line: for all endomorphisms `φ` and `ψ` there is a rational polynomial `R` with `R.natDegree ≤ 2 * g` such that `δ (n • φ + ψ) = R.eval n` for every natural number `n`.

Here `n • φ` is the natural-number multiple in the additive group `A ⟶ A`, and the sum is the sum in that group. `IsIsogeny β` is the Library's finite, flat and surjective predicate on the underlying morphism, and `Scheme.Hom.finrank` is Mathlib's rank of a morphism at a point of its target.

The statement does not say what `δ` is on endomorphisms that are not isogenies.

## Source

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers.

- p. 12, Section 8, after Proposition 8.1: the degree of an isogeny is the rank of `f_* 𝒪_A`; Proposition 8.1(d) identifies isogenies with finite flat surjective homomorphisms.
- p. 21, Proposition 12.4: `deg` extends to a homogeneous polynomial function of degree `2g` on `End⁰(A)`, where Milne sets `deg φ = 0` for endomorphisms that are not isogenies. The proof first reduces to showing that `deg(nφ + ψ)` is a polynomial of degree at most `2g` in `n` for fixed `φ, ψ ∈ End(A)`. It then computes `deg(nφ + ψ)·(D^g) = (D_n^g)` with `D_n = (nφ + ψ)^* D` for a very ample divisor `D`, and shows that `D_n` is quadratic in `n` by the theorem of the cube (Corollary 6.5).

The present proposition is the line form in the first step of that proof. It is weaker than Milne's statement in one respect: `δ` is not required to vanish on endomorphisms that are not isogenies. Milne's degree function satisfies both properties, so Milne's Proposition 12.4 implies this proposition. A proof may replace the intersection number `(D^g)` by the leading coefficient of the Euler characteristic `n ↦ χ(M^n)`. Without the vanishing requirement it need not compute that coefficient for non-isogenies.

## Scope

The field is algebraically closed and of any characteristic. The relative-dimension hypothesis `A.HasRelativeDimension g` fixes the `g` in the degree bound `2 * g`.
