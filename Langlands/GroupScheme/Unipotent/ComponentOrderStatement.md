# The component group of a unipotent group

`Langlands.GroupScheme.UnipotentComponentOrderStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field and `p : ℕ` with `[ExpChar k p]`. Let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. The proposition
says

```text
IsUnipotent G → ∃ n : ℕ, Nat.card (IdentityComponent.GeometricComponents k G) = p ^ n
```

In words, the order of `π₀(G)` of a unipotent affine algebraic group is a
power of the characteristic exponent of `k`.

The ingredients are existing declarations, used without change.

- `ExpChar k p` (Mathlib) says that `p` is the characteristic exponent of `k`:
  `p = 1` if `k` has characteristic `0`, and otherwise `p` is the
  characteristic.
- `IsUnipotent G` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that every nonzero finite-dimensional matrix representation of `G` has a
  nonzero fixed vector.
- `IdentityComponent.GeometricComponents k G` (from
  [`GeometricComponents`](../GeometricComponents.md)) is the type of
  connected components of the underlying topological space of the base change
  of `G` along `Spec(AlgebraicClosure k) → Spec k`. It is defined without any
  smoothness hypothesis; the group structure and the `Finite` instance in that
  module, which need smoothness, are not used. `Nat.card` is its number of
  elements. It is finite because the base change is of finite type over a
  field, so `Nat.card` is the number of connected components of `G_{k^a}`.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 14.15, p.283: "Let G be an algebraic group over k. If G is
  unipotent, then π₀(G) has order a power of the characteristic exponent of
  k; in particular, G is connected if k has characteristic zero."
- Proposition 2.37, p.51: "(b) The kernel of the homomorphism in (a) is G°;
  there is an exact sequence e → G° → G → π₀(G) → e." and "(d) The fibres of
  |G| → |π₀(G)| are the connected components of |G|. The order of the finite
  algebraic group π₀(G) is the number of connected components of G_{k^s}
  (and also of G_{k^a})."
- Chapter 14 opening, p.279: "Recall that all algebraic groups are affine
  over a base field k."
- 6.45, p.135: "An algebraic group G is said to be unipotent if every nonzero
  representation of G has a nonzero fixed vector."
- "Conventions and notation", p.3: "The characteristic exponent of k is p or
  1 according as its characteristic is p or 0."

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 14.15 on
printed p.283 with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for printed pp.274–316. The 2017
errata have no entry for pp.3 or 135. For p.51 the 2017 errata say "Replace X
with G thrice in the first paragraph of Section 2g", and the 2022 errata say
that the map `G(k^s) → π₀(G_{k^s})` in the first paragraph of Section 2g need
not be surjective and that `π₀(G)` is better defined by applying the functor
`π₀` to the group structure. Both concern the construction of `π₀(G)` before
Proposition 2.37, not statement (d) used here.

Milne's proof: "As π₀(G) is a quotient of G, it is unipotent, and so we can
apply the proposition", that is, Proposition 14.14 on finite étale groups,
applied to `π₀(G)`. This is explanation only. The statement does not depend
on that route.

## Derivation from the source

- **Algebraic group.** Milne's algebraic group is a group scheme of finite
  type over `k`, affine by the Chapter 14 convention. The statement assumes
  `LocallyOfFiniteType G.X.hom` and `IsAffineHom G.X.hom`; an affine morphism
  is quasi-compact, so `G` is of finite type over `k`.
- **Unipotent.** Milne's definition is 6.45, which is `IsUnipotent`; its
  comparison is recorded in [`Reductive.Basic`](../Reductive/Basic.md).
- **Order of `π₀(G)`.** By Proposition 2.37(d), the order of `π₀(G)` is the
  number of connected components of `G_{k^a}`. With `k^a` Mathlib's
  `AlgebraicClosure k`, this is
  `Nat.card (IdentityComponent.GeometricComponents k G)`.
- **Characteristic exponent.** Milne's characteristic exponent is Mathlib's
  `ExpChar k p`, and `p` is universally quantified with this instance. "A
  power of `p`" is `∃ n : ℕ, order = p ^ n`.
- **Scope.** The clause "in particular, G is connected if k has
  characteristic zero" is not part of this statement. For `p = 1` the
  statement says that `G_{k^a}` is connected. The connectedness of `G`
  itself in characteristic zero is the Library statement
  `Langlands.GroupScheme.CharZeroUnipotentConnectedStatement` (in
  [`Unipotent.CharZeroConnectedStatement`](CharZeroConnectedStatement.md)).
- **Universes.** One universe `u` is used for `k` and the schemes. This is a
  formalization convention.
