# Split tori are reductive: statements

This module states two theorems about split tori, in the sense of `IsSplitTorus` from
`Langlands.GroupScheme.Torus.Split`. They use the notions of `Langlands.GroupScheme.Reductive.Basic`.
The module proves neither. The third declaration, `ReductiveStatement`, is their conjunction. All
three declarations are `Prop`-valued definitions in the namespace
`Langlands.GroupScheme.IsSplitTorus`, with one universe parameter `u`.

A group scheme `G` over `S` is a split torus (`IsSplitTorus G`) when it is isomorphic, as a group
scheme over `S`, to `splitTorus S I` for some finite index type `I : Type u`. `splitTorus S I` is
the product of copies of `Gm S` indexed by `I`. The empty index type is allowed, and then `G` is
the trivial group.

## `IsConnectedReductiveStatement`

For every field `k : Type u` and every group scheme `G` over `Spec k`, if `G` is a split torus then
`G` satisfies `IsConnectedReductive`. Unfolding that structure, `G` is smooth, affine and connected
over `Spec k`. Its base change to `AlgebraicClosure k` has trivial unipotent radical: every smooth
connected unipotent closed subgroup with normal image is trivial.

## `IsReductiveStatement`

For every scheme `S : Scheme.{u}` and every group scheme `G` over `S`, if `G` is a split torus then
`G` satisfies `IsReductive`. That is, `G` is smooth and affine over `S`, and for every point `s` of
`S` its geometric fibre is pseudo-reductive. The geometric fibre is the base change along
`Spec κ(s)^alg → S` (`geometricFiber`). Over an algebraically closed field, pseudo-reductive is
the same as connected reductive.

## `ReductiveStatement`

`ReductiveStatement` is `IsConnectedReductiveStatement ∧ IsReductiveStatement`, in the same
universe `u`. It is the single target for a proof of both statements.

## Sources

- Milne, *Algebraic groups* (2017), Definition 12.14 (printed p. 236, PDF p. 252): a torus over
  `k` is split if it is isomorphic to a product of copies of `Gm` over `k`. This is `IsSplitTorus`
  over `Spec k`.
- Milne, *Algebraic groups* (2017), Corollary 19.18 (printed p. 401, PDF p. 417): "A connected
  group variety G is reductive if it admits a faithful semisimple representation that remains
  semisimple over k^a." Milne's reductive groups are the connected ones of 6.46 (printed p. 135),
  as in `IsConnectedReductive`. Milne does not state the torus case as a numbered result. It is
  derived from Corollary 19.18: a split torus `Gm^n` is a connected group variety, and its
  diagonal embedding into `GL_n` is a faithful representation that is a sum of one-dimensional
  representations, over `k` and over `k^a`. Theorem 12.12 (printed p. 234, PDF p. 250) says that
  every representation of a diagonalizable group is such a sum.
- Conrad, *Reductive group schemes* (2014), Definition 3.1.1 (p. 81): a reductive group over a
  scheme `S` is a smooth `S`-affine group whose geometric fibres are connected reductive groups.
  The second statement is that definition applied to a split torus over `S`. Its content beyond
  the first statement is that split tori are affine over every base and that their geometric
  fibres are split tori over algebraically closed fields. Conrad treats this as standard (the same
  definition calls an `S`-torus a group of multiplicative type with smooth connected fibres); it is
  derived here from the field case.
