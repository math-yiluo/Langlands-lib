# Anisotropic almost-simple factors centralize the maximal split torus

Authors: Worker 1526.

`Langlands.GroupScheme.SimplyConnectedAnisotropicFactorCentralizerStatement.{u}`
is a proposition definition, not a proof. Let `G` be a simply connected group
over a field `k`, with a maximal split torus `S`. The proposition states that
every anisotropic closed normal almost-simple subgroup `A` of `G` centralizes
`S`: on every test scheme, every point of `A` commutes with every point of
`S`.

## The proposition

For every `k : Type u` with `[Field k]`, every
`G : GroupScheme (Spec (CommRingCat.of k))` with `IsSimplyConnected G`, every
`S : CommGroupScheme (Spec (CommRingCat.of k))` and `i : S.toGrp ⟶ G` with
`IsMaximalSplitTorus i`, and every `A : GroupScheme (Spec (CommRingCat.of k))`
and `a : A ⟶ G` with `IsAlmostSimple A`, `IsClosedSubgroup a`,
`(SubgroupFunctor.range a).IsNormal` and `IsAnisotropic A`,

```
SubgroupFunctor.range a ≤ torusCentralizer i
```

as subgroup functors of `G`.

These are all the quantified data and hypotheses. The universe `u` is
arbitrary, and the field `k` is arbitrary: no characteristic, perfectness or
topology hypothesis is made. No new definition is introduced. The derivation
below does not use the maximality of `S`, only that `S` is a split torus;
the hypothesis `IsMaximalSplitTorus i` is kept to match the intended use.

## Exact objects

- `IsSimplyConnected G` (module `Langlands.GroupScheme.SimplyConnected.Basic`)
  says that `G` is semisimple and that every central isogeny onto `G` from a
  semisimple group is an isomorphism.
- `IsMaximalSplitTorus i` (module `Langlands.GroupScheme.Rational.SplitTorus`)
  says that `i` is a closed immersion of a split torus and that every
  factorization of `i` through another closed split torus is an isomorphism.
- `IsAlmostSimple A` (module `Langlands.GroupScheme.Reductive.AlmostSimple`)
  says that `A` is semisimple, is not commutative, and that every smooth
  connected closed subgroup of `A` with normal range has range trivial or all
  of `A`. This is Milne's definition 19.7 of an almost-simple group over `k`.
- `IsClosedSubgroup a` (module `Langlands.GroupScheme.Reductive.Basic`) says
  that the underlying morphism of schemes of `a` is a closed immersion.
- `(SubgroupFunctor.range a).IsNormal` and `SubgroupFunctor.range a` (module
  `Langlands.GroupScheme.SubgroupFunctor`): `SubgroupFunctor.range a` is the
  subgroup functor of `G` whose value on a test scheme `T` is the image of
  `A(T)` in `G(T)`, and `IsNormal` says that each of these images is normal.
- `IsAnisotropic A` (module `Langlands.GroupScheme.Rational.SplitTorus`) says
  that the split rank `splitRank A` is `0`, that is, `A` has no closed split
  subtorus of positive dimension.
- `torusCentralizer i` (module `Langlands.GroupScheme.Rational.TorusCentralizer`)
  is the subgroup functor of `G` whose value on a test scheme `U` is the set
  of `g ∈ G(U)` such that for every `V` over `U`, the restriction of `g` to
  `V` commutes with `i(t)` for every `t ∈ S(V)`. It is the functor of points
  of the centralizer `Z_G(S)`.
- `≤` is the order on subgroup functors of `G`: containment on every test
  scheme.

## Source and derived formulation

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field*, Cambridge University Press, corrected reprint 2022, registered
as `milne-2022-algebraic-groups`. Printed page = PDF page − 11.

- Theorem 21.51, printed pp. 439–441 / PDF pp. 450–452: a semisimple group
  `G` over a field is the almost-direct product of its finitely many
  almost-simple normal subgroups `G_1, …, G_r`, the `G_i` commute in pairs,
  and every smooth connected normal subgroup of `G` is the product of the
  `G_i` it contains.
- Printed p. 236 / PDF p. 247, after Definition 12.14: a quotient of a split
  torus is a split torus.

G. Prasad and M. S. Raghunathan, *On the Kneser–Tits problem*, Comment.
Math. Helv. 60 (1985), 107–121, registered as
`prasad-raghunathan-1985-kneser-tits`, §1.5, printed p. 108 / PDF p. 3: a
semisimple simply connected `k`-group is the direct product of its connected
`k`-simple normal subgroups.

The proposition is a derived formulation and not a numbered result. The
following standard argument is its provenance; it is not proved here.

1. As in step 1 of the Markdown of
   `Langlands.GroupScheme.SimplyConnectedKneserTitsFactorStatement`, the
   image of `a` is one almost-simple normal factor `G_1` of `G`, and `a` is
   an isomorphism onto it (Milne 21.51). Since `G` is simply connected,
   `G = A × G'` with `G' = G_2 × ⋯ × G_r` (PR85 §1.5). Every point of `A`
   commutes with every point of `G'`, on every test scheme.
2. Let `p : G → A` be the projection. The image of the split torus `S`
   under `p ∘ i` is a quotient of `S`, hence a split torus (Milne, printed
   p. 236), and it is a closed subgroup of `A`. Since `A` has split rank
   `0`, this image is trivial. So `i(S)` lies in the kernel `G'` of `p`.
3. By steps 1 and 2, every point of `A` commutes with every point of
   `i(S)`, on every test scheme. So the range of `a` lies in
   `torusCentralizer i`.

This module supplies no proof. The proof is a separate obligation.

Intended use (a remark, not proved in this module): together with
`Langlands.GroupScheme.SimplyConnectedAlmostSimpleRationalGenerationStatement`
and `Langlands.GroupScheme.SimplyConnectedKneserTitsFactorStatement`, this
proposition is an input for deriving
`Langlands.GroupScheme.SimplyConnectedKneserTitsCentralizerStatement`.
