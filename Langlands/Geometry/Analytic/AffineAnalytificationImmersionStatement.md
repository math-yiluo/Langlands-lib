# Statement: analytification of affine closed and open immersions

`AffineAnalytificationImmersionStatement` states three topological facts about
the Library's polynomial-locus affine analytification and the maps `baseMap`
induced by `K`-algebra maps:

1. a surjective algebra map induces a closed embedding;
2. a localization away from one element induces an open embedding;
3. the image of that open embedding is the complement of the image of the
   closed embedding induced by the quotient by the same element.

This is a statement only; its proof is a separate successor.

## Source

Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*
(1990). The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

- Proposition 3.4.7(2), printed p.66/PDF p.80: for a morphism of finite type
  `g`, `g` is a closed immersion if and only if `g^an` is. The forward
  direction is proved "by the proof of Theorem 3.4.1".
- Proposition 3.4.6(8), printed p.65/PDF p.79, with its proof on printed
  p.66/PDF p.80: `g` is an open immersion if and only if `g^an` is. The forward
  direction is again proved by the proof of Theorem 3.4.1.
- Proof of Theorem 3.4.1, step (2), printed p.64/PDF p.78. For an open
  subscheme `X` of `Y`, `X^an` is the open subset `π⁻¹(X)` of `Y^an`. For a
  closed subscheme `X` of `Y`, `X^an` is the closed analytic subspace defined
  by the ideal `J^an`.
- Proof of Proposition 3.4.4, printed p.65/PDF p.79. For the reduced closed
  subscheme `Y` complementary to an open subset `T` of `X`,
  `|Y^an| = |X^an| \ π⁻¹(T)`.
- Remark 3.4.2, printed p.64/PDF p.78: for `X = Spec A`, the space `X^an` is
  the set of multiplicative seminorms on `A` extending the norm of `k`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, proof of Proposition 5.11(3), final paragraph, uses that the
analytification functor is compatible with open and closed immersions. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The Lean statement covers only the affine case, and only the underlying
continuous maps of the forward implications. An open or closed immersion of
analytic spaces is in particular an open or closed embedding of underlying
topological spaces. The open immersion is stated for a principal open
`Spec A_g ⊆ Spec A`, and the complement identity for the quotient `A/(g)`,
which need not be reduced. Statements about the underlying sets do not depend
on reducedness. The formulation through `baseMap` and arbitrary finite
polynomial presentations is derived.

## Hypotheses

The field `K` is nontrivially normed, ultrametric and complete. `A` is any
commutative `K`-algebra with an arbitrary finite polynomial presentation
`P : FinitePolynomialPresentation K A`.

1. `B` is any commutative `K`-algebra with any finite polynomial presentation
   `Q`, and `f : A →ₐ[K] B` is any surjective `K`-algebra map.
2. `g : A` is arbitrary, including nilpotent `g`, which gives `B = 0`. `B` is
   any `A`-algebra satisfying `IsLocalization.Away g B`, with its `K`-algebra
   structure compatible through `IsScalarTower K A B`, and `Q` is any finite
   polynomial presentation of `B`.
3. In addition to the data of item 2, `C` is any `A`-algebra with compatible
   `K`-algebra structure (`IsScalarTower K A C`). Its structure map `A → C` is
   surjective with kernel exactly `Ideal.span {g}`, and `R` is any finite
   polynomial presentation of `C`.

## The claims

- `IsClosedEmbedding (baseMap K P Q f)` whenever `Function.Surjective f`.
- `IsOpenEmbedding (baseMap K P Q (IsScalarTower.toAlgHom K A B))`.
- `range (baseMap K P Q (IsScalarTower.toAlgHom K A B)) =
  (range (baseMap K P R (IsScalarTower.toAlgHom K A C)))ᶜ`.

Here `baseMap K P Q f : C(Space K Q, Space K P)` is defined in
`AffineAnalytificationMap`. On each bounded chart of `Q` it pulls back
multiplicative seminorms along the chart map induced by `f`. `Space` is the
glued space of bounded polynomial loci from `AffineAnalytificationGluing`.

## Why the claims are expected to hold

Truth check, not the proof. As in Remark 3.4.2, a point of `Space K P` amounts
to a multiplicative seminorm `x` on `A` extending the norm of `K`. Indeed, a
seminorm with all `|Tᵢ(x)| ≤ r` is bounded by the Gauss norm on polynomials,
so it extends to the closed relation quotient of the radius-`r` Tate algebra.
The topology of `Space K P` agrees with the weakest topology making every
`x ↦ x(a)` continuous: both topologies agree on each compact chart, and the
open polydiscs are open in both. Under this description `baseMap` is
precomposition with `f`.

1. If `f` is surjective, precomposition is injective. Its image is the closed
   set of seminorms vanishing on `ker f`, and the weak topologies correspond.
2. A seminorm `x` on `A` with `x(g) ≠ 0` extends uniquely to `A_g` by
   `a/gⁿ ↦ x(a)/x(g)ⁿ`. Any extension lies in some bounded chart of `Q` because
   the radii are unbounded. So the image is the open set `{x(g) ≠ 0}`, and the
   formula makes the inverse continuous.
3. The kernel of a multiplicative seminorm is a prime ideal. Hence `x` factors
   through `A/(g)` exactly when `x(g) = 0`.

## Scope

The statement does not assert the converse implications of Propositions
3.4.6(8) and 3.4.7(2). It says nothing about the analytic structure: no
statement about `atlasHom`, `strongHom`, local rings or closed analytic
subspaces. It does not cover general open subschemes, nonaffine schemes or
algebraic spaces. It also does not identify `Space K P` with the set of
multiplicative seminorms on `A`; that identification is used above only as an
informal truth check.
