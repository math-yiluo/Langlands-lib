# Unipotent groups in characteristic zero are connected

Author: Worker 4246.

`Langlands.GroupScheme.CharZeroUnipotentConnectedStatement.{u}` is a proposition
definition; this module supplies no proof. It records the characteristic-zero clause of
Milne's Corollary 14.15.

## The statement

For every field `k : Type u` of characteristic zero (`[Field k] [CharZero k]`) and every group
scheme `G : GroupScheme (Spec k)` (a group object in schemes over `Spec k`) with

- `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`: `G` is affine and locally of finite
  type, hence of finite type, over `k`, that is, an affine algebraic group in Milne's sense;
- `IsUnipotent G` (`Langlands/GroupScheme/Reductive/Basic.lean`): every matrix representation
  `G ⟶ GL_n` with `n` nonempty has a nonzero fixed vector,

the conclusion is `ConnectedSpace G.X.left`: the underlying topological space of `G` is
connected (and nonempty, as `G` has the unit point).

## Source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field*
(2022 corrected reprint), registered source `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`, Corollary 14.15,
printed p.283 (one-based PDF p.294):

> Let G be an algebraic group over k. If G is unipotent, then π₀(G) has order a power of the
> characteristic exponent of k; in particular, G is connected if k has characteristic zero.

The Lean proposition is the final clause, "G is connected if k has characteristic zero".

## Correspondence

Milne's algebraic groups are group schemes of finite type over `k`. The hypotheses
`IsAffineHom` and `LocallyOfFiniteType` express that `G` is an affine algebraic group, so the
Lean proposition is the affine case of the corollary. `IsUnipotent` is the Library's
predicate. Milne, §14.b, printed p.280 (PDF p.291), recalls from 6.45: "an algebraic group G
is unipotent if every nonzero representation of G has a nonzero fixed vector", and notes that
"it suffices to check the condition for finite-dimensional representations". A
finite-dimensional representation of `G` on `k^n`, written in the standard basis, is a matrix
representation `G ⟶ GL_n` as in the Library predicate. "Connected" means that the underlying
topological space of `G` is connected.

The official errata snapshot `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`, was read; it has no entry
for printed p.283. The declaration name is derived here.
