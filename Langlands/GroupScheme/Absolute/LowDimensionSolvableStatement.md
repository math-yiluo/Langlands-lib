# Statement: group varieties of dimension at most two are solvable

Worker 75.

`Langlands.GroupScheme.LowDimensionSolvableStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Absolute.Borel`](Borel.md), for `IsSolvableGroupScheme` and the group-scheme vocabulary
  over a field.
- [`Lie.DimensionInduction`](../Lie/DimensionInduction.md), for `Lie.dimension`.

## Lean statement

```lean
def LowDimensionSolvableStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    Lie.dimension G ≤ 2 → IsSolvableGroupScheme G
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `Lie.dimension G` ([`Lie.DimensionInduction`](../Lie/DimensionInduction.md)): the
  `k`-dimension (`Module.finrank`) of the Lie algebra of `G`, the kernel of
  `G(k[ε]) → G(k)` for the dual numbers `k[ε]`. This is the dimension of the tangent space of
  `G` at the identity.
- `IsSolvableGroupScheme G` ([`Absolute.Borel`](Borel.md)): the abstract group of points of `G`
  over an algebraic closure of `k` is solvable. This is the Library's solvability predicate for
  smooth groups over a field.

## Statement and quantifiers

For every algebraically closed field `k : Type u` and every smooth, affine, connected group
scheme `G` over `Spec k` whose Lie algebra has dimension at most `2`, the group `G` is
solvable.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.27, p.360: "If dim(G) ≤ 2, then G is solvable."
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Proposition 1.37, p.18: "For an algebraic group G, dim Tgt_e(G) ≥ dim G, with equality if and
  only if G is smooth."
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; p.13:
  "group variety" = "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. The p.360 entry corrects the sentence after this corollary to "SL₂ (not SL₃) has
dimension 3"; it does not change Corollary 17.27.

Milne's proof: a Borel subgroup `B` of dimension `0` or `1` is nilpotent, so `G = B` by
Proposition 17.23; if `dim B = 2` then `G = B`. This is explanation only.

## Derivation from the source

- **Connected group variety.** As in Section 17b: `[IsAlgClosed k]`, `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **Dimension.** Milne's `dim G` is the dimension of `G` as a scheme. Since `G` is smooth,
  Proposition 1.37 gives `dim G = dim Tgt_e(G)`, and the tangent space at `e` is the Lie
  algebra measured by `Lie.dimension`. So `Lie.dimension G ≤ 2` is Milne's hypothesis.
- **Solvability.** For smooth groups the Library measures solvability through the abstract
  group of `k̄`-points; here `k` is algebraically closed, where this agrees with Milne's notion
  for group varieties.

## Scope

- The bound `2` is sharp: by the errata, `SL₂` has dimension `3` and is not solvable. That
  example is not stated.

## Related Library results

- [`Absolute.BorelStatement`](BorelStatement.md) states existence and conjugacy of Borel
  subgroups (17.9).
