# Pseudo-reductivity under separable algebraic extension

`Langlands.GroupScheme.PseudoReductiveSeparableExtensionStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves nothing.

## Statement

The proposition says: for all fields `k K : Type u` in one universe `u`, with
`[Algebra k K]` and `[Algebra.IsSeparable k K]`, and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))`,

```text
IsPseudoReductive G →
  IsPseudoReductive
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).
```

In words: if `G` is pseudo-reductive over `k` and `K/k` is a separable algebraic
field extension, then the base change `G_K` is pseudo-reductive over `K`.

Every ingredient is an existing declaration, used without change:

- `IsPseudoReductive` (from `Langlands.GroupScheme.Reductive.Basic`) is a structure
  with four fields: `Smooth G.X.hom`, `IsAffineHom G.X.hom`,
  `ConnectedSpace G.X.left` and `HasTrivialUnipotentRadical G`. The last field says
  that for every group scheme `H` over `Spec k` and every homomorphism `i : H ⟶ G`
  that is a closed immersion, if `H` is smooth, connected and unipotent and the
  image subgroup functor `SubgroupFunctor.range i` is normal, then
  `SubgroupFunctor.range i = ⊥`. Only subgroups defined over the ground field
  itself are tested.
- `GroupScheme.baseChange f` (from `Langlands.AbelianScheme.GroupScheme`) is
  `(Over.pullback f).mapGrp`: the actual scheme pullback with its induced group
  law. Here `f` is `Spec K ⟶ Spec k`, induced by `algebraMap k K`.
- `Algebra.IsSeparable k K` is Mathlib's class: every element of `K` is separable
  over `k`. Separable elements are integral, so `K/k` is algebraic. Mathlib records
  this as the instance `Algebra.IsSeparable.isAlgebraic`.

The statement adds no further hypotheses on `k`, `K` or `G`. In particular it
requires no perfectness, finiteness or Galois condition, and `G` may be any group
scheme over `Spec k` satisfying `IsPseudoReductive`. The conclusion is the full
predicate for `G_K`: smoothness, affineness, connectedness and the trivial
`K`-unipotent radical. For example, the statement covers `K = SeparableClosure k`
and every finite separable extension. It does not cover separable transcendental
extensions.

## Provenance (derived)

Source: B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second
edition (2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`
(SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`),
Proposition 1.1.9(1), printed p. 8 (PDF p. 34).

The source states it for a separable extension of fields `K/k`, which need not be
algebraic, and a smooth connected affine `k`-group `G`. It says: inside `G_K` we
have `R_{u,k}(G)_K = R_{u,K}(G_K)`. In particular, `G` is pseudo-reductive over
`k` if and only if `G_K` is pseudo-reductive over `K`.

This module formalizes part of the "in particular" clause, so its provenance is
derived:

1. It states only the direction from `k` to `K`.
2. It restricts to separable *algebraic* extensions, the case encoded by
   Mathlib's `Algebra.IsSeparable`.
3. It does not state the equality of unipotent radicals, since the Library has no
   chosen radical object. Pseudo-reductivity is expressed through
   `HasTrivialUnipotentRadical`, which matches CGP Definition 1.1.1 (printed p. 3,
   PDF p. 29). `R_{u,k}(G)` is the maximal smooth connected unipotent normal
   `k`-subgroup, so it is trivial exactly when every such subgroup is trivial.
4. Both fields lie in one universe `u`. This is a formalization convention that
   the source does not impose.

In the source, "`G_K` is pseudo-reductive" includes that `G_K` is again a smooth
connected affine `K`-group. That is why the conclusion here includes smoothness,
affineness and connectedness of `G_K`. Smoothness and affineness are stable under
base change. Connectedness survives because a connected group scheme over a field
is geometrically connected: it has the rational point given by the identity. These
standard facts are not proved in Proposition 1.1.9 itself, and this module proves
none of them.

For the later proof (not part of this unit): the source proof, printed p. 9
(PDF p. 35), first handles Galois extensions `k'/k` by Galois descent of
`R_{u,k'}(G_{k'})` to a smooth connected unipotent normal `k`-subgroup of `G`.
For a separable algebraic `K/k`, a smooth connected unipotent normal
`K`-subgroup of `G_K` descends to a finite subextension. That subextension lies in
a finite Galois extension of `k`.

Use downstream: the proof of Proposition C.1.6, printed p. 586 (PDF p. 612),
reduces to `k = k_s` because "it is harmless to make a separable extension on
`k`". It then uses pseudo-reductivity of `G` over `k_s`. This relies on
Proposition 1.1.9(1) for `K = k_s`, without citing it explicitly.
