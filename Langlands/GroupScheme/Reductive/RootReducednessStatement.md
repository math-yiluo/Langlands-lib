# Statement: the roots of a split maximal torus are reduced

`Langlands.GroupScheme.RootReducednessStatement` is an unproved proposition at
arbitrary universe `u`. Nothing is proved in this module.

## The statement

Let `k : Type u` be a field and `G` a group scheme over `Spec k` satisfying the
published `IsConnectedReductive G`. Let `T` be a commutative group scheme with
`IsSplitTorus T.toGrp`, and let `i : T.toGrp ⟶ G` satisfy `IsMaximalTorus i`.
These are exactly the hypotheses of `RootDatumExistenceStatement` in
`Langlands.GroupScheme.Reductive.RootDatumStatement`. The instance
`IsAffineHom G.X.hom`, which `roots i` needs, comes from `hG.isAffineHom`, as in
that statement.

The conclusion: for all `α β ∈ roots i`, if `![α, β]` is not linearly independent
over `ℤ` in `characterLattice T`, then `α = β` or `α = -β`. Here `roots i` is the
published set of nonzero characters of `T` with a nonzero weight space in the
actual Lie algebra `Lie(G)(k)` (`Langlands.GroupScheme.roots`).

## Relation to the source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- §21.c, printed p.428 (PDF 444): a root datum is *reduced* if, for every
  `α ∈ Φ`, the only rational multiples of `α` in `Φ` are `±α`.
- Theorem 21.11(b), printed p.428 (PDF 444), proof printed p.429 (PDF 445):
  for a split reductive group `(G, T)` over `k` and a root `α` of `(G, T)`,
  the only rational multiples of `α` in `Φ(G, T)` are `±α`.
- Corollary 21.12, printed p.430 (PDF 446): the root datum of `(G, T)` is
  reduced, by Theorem 21.11(b).

The author's errata page (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists no correction to these
three passages.

Milne's split reductive group `(G, T)` is a reductive group `G` with a split
maximal torus `T`, and `Φ(G, T)` is the set of nonzero weights of `T` on
`Lie(G)`. These are the hypotheses above and the published `roots i`.

The Lean conclusion is Milne's assertion in the form of Mathlib's
`RootPairing.IsReduced`, applied to the actual root set. The two forms agree.
Roots are nonzero by definition, and the character lattice of a split torus is
torsion-free. So, for roots `α` and `β`, the pair `![α, β]` is linearly
dependent over `ℤ` exactly when `n • β = m • α` for some integers `m` and
`n ≠ 0`, that is, when `β` is a rational multiple of `α`. A zero coefficient on
`β` is impossible, because it would force a nonzero multiple of `α` to vanish.

This form is chosen so that the reducedness clause of
`RootDatumExistenceStatement` follows directly. If a root datum `P` satisfies
`Set.range P.root = roots i`, as `IsRootDatumOf i P` requires, then this
statement gives `P.IsReduced` through `RootPairing.isReduced_iff`.

## Scope

The statement asserts only that the actual roots are reduced. It does not
assert that `-α` is a root, that `dim g_α = 1`, or anything about coroots or
reflections. It assumes no root datum and no rank-one classification. Milne
derives Theorem 21.11(b) from the structure of the semisimple-rank-one group
`G_α = C_G(T_α)`, using the homomorphisms `SL₂ → G_α → PGL₂` of 20.32.
