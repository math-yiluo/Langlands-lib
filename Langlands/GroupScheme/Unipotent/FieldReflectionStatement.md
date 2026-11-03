# Unipotence descends along a field extension: statement

Author: Worker 1487.

`UnipotentFieldReflectionStatement.{u}` states that for fields `k K : Type u`,
an algebra structure `Algebra k K`, and an affine group scheme `G` over
`Spec k`, unipotence of the actual pullback of `G` along `Spec K → Spec k`
implies `IsUnipotent G`. The universe is arbitrary, and the fields may be
finite or imperfect and of any characteristic. The statement requires no
smoothness or connectedness.

`IsUnipotent` is the published predicate from `Reductive.Basic`: every
nonzero finite-dimensional matrix representation has a nonzero fixed vector
on every test scheme. The pullback is the published `GroupScheme.baseChange`
applied to the spectrum map induced by `algebraMap k K`.

This file defines a proposition and proves nothing. Together with the
published `IsUnipotent.baseChange` from `Unipotent.BaseChange`, a proof would
give both directions of invariance under field extension. In particular,
it would justify passing from a nonunipotent group to its nonunipotent
base change in the finite-field branch of Milne's Proposition 17.81.

## Provenance and source boundary

This is an internal generalization of the reflection direction of Milne,
*Algebraic Groups* (2017), Corollary 14.9, printed p.282 (one-based PDF
p.298), source ID `milne-2017-algebraic-groups`. Milne states the equivalence
for algebraic groups, which are affine group schemes of finite type in this
part of the book. The present proposition drops finite type. Its proposed
coordinate proof needs only the already published equivalence between
`IsUnipotent` and the coordinate-bialgebra predicate `Unipotent.OneMemStable`,
and descent of that predicate by linear algebra. It does not appeal to a
finite-dimensional faithful representation of `G`.

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was read in full. Its
Chapter 14 entry does not alter Corollary 14.9.
