# Degree of an endomorphism as a rational Tate determinant

`Langlands.AbelianScheme.IsogenyDegreeTateDeterminantStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. The statement quantifies over:

- every algebraically closed field `k : Type u`;
- every abelian scheme `A` over `Spec k`;
- every prime `p` with `(p : k) ≠ 0`, that is, `p` different from the characteristic of `k`;
- every actual endomorphism `α : A ⟶ A`.

Write `V_p(α)` for `Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α`. This is the existing `ℚ_[p]`-linear endomorphism that `α` induces on the actual rational `p`-adic Tate module `Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p` of the `k`-points of `A`. The statement has two conclusions.

1. If `α` is an isogeny (`IsIsogeny α`), then at every point `y` of the scheme `A.X.left`, the rank `(hom α).finrank y` of the finite flat underlying morphism, cast to `ℚ_[p]`, equals `LinearMap.det (V_p(α))`.
2. If `α` is not an isogeny, then `LinearMap.det (V_p(α)) = 0`.

Here `IsIsogeny α` is the Library's finite, flat and surjective predicate on the underlying morphism, and `Scheme.Hom.finrank` is Mathlib's rank of a morphism at a point of its target.

## Source

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers.

- p. 12, Section 8. Proposition 8.1(d) shows that an isogeny is the same as a finite, flat and surjective homomorphism, which is the Library's `IsIsogeny`. The paragraph after its proof defines the degree of an isogeny `f : A → B` as the rank of the locally free `𝒪_B`-module `f_* 𝒪_A`. Conclusion 1 uses this rank in the form of Mathlib's `finrank` of the underlying finite flat morphism.
- p. 21, Section 12. For `α ∈ End(A)`, `deg α` is the degree of `α` if `α` is an isogeny, and `deg α = 0` otherwise. Conclusion 2 is the case `deg α = 0`.
- p. 23, Proposition 12.9. For every prime `l ≠ char(k)`, the degree of `α` is the determinant of `α` acting on `ℚ_l ⊗ T_l A`.

So the two conclusions together state the degree part of Proposition 12.9 for actual endomorphisms, with Milne's convention that a non-isogeny has degree `0`. The trace part of Proposition 12.9 is not stated.

## Scope

Milne proves Proposition 12.9 after reducing to a separably closed field. Here the field is assumed algebraically closed, so the `k`-points of `A` compute Milne's Tate module. The prime is any prime invertible in `k`, as in Milne. The statement concerns only the existing actual Tate module at the base point `Over.mk (𝟙 _)`. It assumes neither finite-dimensionality of that module nor a relative-dimension hypothesis.
