# Degree of an endomorphism as a rational Tate determinant in characteristic zero

`Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. The statement quantifies over:

- every algebraically closed field `k : Type u` of characteristic zero (`[CharZero k]`);
- every abelian scheme `A` over `Spec k`;
- every prime `p`;
- every actual endomorphism `α : A ⟶ A`.

Write `V_p(α)` for `Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α`. This is the existing `ℚ_[p]`-linear endomorphism that `α` induces on the actual rational `p`-adic Tate module `Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p` of the `k`-points of `A`. The statement has two conclusions.

1. If `α` is an isogeny (`IsIsogeny α`), then at every point `y` of the scheme `A.X.left`, the rank `(hom α).finrank y` of the finite flat underlying morphism, cast to `ℚ_[p]`, equals `LinearMap.det (V_p(α))`.
2. If `α` is not an isogeny, then `LinearMap.det (V_p(α)) = 0`.

Here `IsIsogeny α` is the Library's finite, flat and surjective predicate on the underlying morphism, and `Scheme.Hom.finrank` is Mathlib's rank of a morphism at a point of its target.

## Source

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers.

- p. 12, Section 8. Proposition 8.1(d) shows that an isogeny is the same as a finite, flat and surjective homomorphism, which is the Library's `IsIsogeny`. The paragraph after its proof defines the degree of an isogeny as the rank of `f_* 𝒪_A`. Conclusion 1 uses this rank in the form of Mathlib's `finrank` of the underlying finite flat morphism.
- p. 21, Section 12. For `α ∈ End(A)`, `deg α` is the degree of `α` if `α` is an isogeny, and `deg α = 0` otherwise. Conclusion 2 is the case `deg α = 0`.
- p. 23, Proposition 12.9. For every prime `l ≠ char(k)`, the degree of `α` is the determinant of `α` acting on `ℚ_l ⊗ T_l A`.

So the two conclusions together state the degree part of Proposition 12.9 for actual endomorphisms, with Milne's convention that a non-isogeny has degree `0`. The trace part of Proposition 12.9 is not stated.

## Relation to `IsogenyDegreeTateDeterminantStatement`

`Langlands.AbelianScheme.IsogenyDegreeTateDeterminantStatement` (module `Langlands/AbelianScheme/IsogenyDegreeTateDeterminantStatement.lean`) states the same two conclusions for every algebraically closed field and every prime `p` with `(p : k) ≠ 0`. The present proposition is its special case for fields of characteristic zero. There every prime satisfies `(p : k) ≠ 0`, so that hypothesis is omitted. The restriction to characteristic zero is a choice of scope, and the statement is weaker than Milne's proposition, which holds in every characteristic. Milne's proof (p. 23) uses `|deg β|_l = |#Ker(β)(k)|_l`. In positive characteristic this needs the inseparable part of the degree to be a power of the characteristic. In characteristic zero every isogeny is étale, and its degree is the number of `k`-points of its kernel.

## Scope

Milne proves Proposition 12.9 after reducing to a separably closed field. Here the field is assumed algebraically closed, so the `k`-points of `A` compute Milne's Tate module. The statement concerns only the existing actual Tate module at the base point `Over.mk (𝟙 _)`. It assumes neither finite-dimensionality of that module nor a relative-dimension hypothesis.
