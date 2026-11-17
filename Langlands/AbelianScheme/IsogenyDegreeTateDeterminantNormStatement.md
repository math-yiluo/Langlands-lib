# The `p`-adic absolute value of the degree of an endomorphism

`Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. The statement quantifies over:

- every algebraically closed field `k : Type u` of characteristic zero (`[CharZero k]`);
- every abelian scheme `A` over `Spec k`;
- every prime `p`;
- every actual endomorphism `α : A ⟶ A`.

Write `V_p(α)` for `Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α`, the existing `ℚ_[p]`-linear endomorphism that `α` induces on the actual rational `p`-adic Tate module `Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p` of the `k`-points of `A`. The statement has two conclusions.

1. If `α` is an isogeny (`IsIsogeny α`), then at every point `y` of the scheme `A.X.left`, the `p`-adic norm of the rank `(hom α).finrank y`, cast to `ℚ_[p]`, equals the `p`-adic norm of `LinearMap.det (V_p(α))`.
2. If `α` is not an isogeny, then `LinearMap.det (V_p(α)) = 0`.

`‖·‖` is the norm of `ℚ_[p]`, that is, the `p`-adic absolute value. `IsIsogeny α` is the Library's finite, flat and surjective predicate on the underlying morphism, and `Scheme.Hom.finrank` is Mathlib's rank of a morphism at a point of its target.

## Source

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers.

- p. 12, Section 8, after Proposition 8.1: the degree of an isogeny is the rank of `f_* 𝒪_A`; Proposition 8.1(d) identifies isogenies with finite flat surjective homomorphisms.
- p. 23, the proof of Proposition 12.9. For every `β ∈ End(A)`, with `k` separably closed and `l ≠ char(k)`, Milne displays

  `|deg(β)|_l = |#Ker(β)|_l = (#Ker(β)(l))^{-1} = (#Coker(T_l β))^{-1} = |det(T_l β)|_l`.

  Conclusion 1 is this chain for an isogeny, with `T_l β` replaced by its rational extension `V_p(α)`, which has the same determinant.
- p. 21, Section 12: `deg β = 0` when `β` is not an isogeny. For such `β` the displayed chain says `|det(T_l β)|_l = 0`, which is conclusion 2.

## Scope

Milne's chain holds in every characteristic for `l ≠ char(k)`. The statement here is restricted to characteristic zero, where every prime is allowed. This is a choice of scope. It is the input needed by the characteristic-zero form of Proposition 12.9, `IsogenyDegreeTateDeterminantCharZeroStatement`. In characteristic zero every isogeny is étale, so its degree is the number of `k`-points of its kernel.

The statement concerns only the existing actual Tate module at the base point `Over.mk (𝟙 _)`. It assumes neither finite-dimensionality of that module nor a relative-dimension hypothesis.
