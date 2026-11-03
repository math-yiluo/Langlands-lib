# Connected reductivity under arbitrary field extension

`Langlands.GroupScheme.ConnectedReductiveFieldExtensionStatement` is a
proposition target. This module defines the proposition and supplies no proof
of it.

For all fields `k K : Type u`, an instance `Algebra k K`, and an actual group
scheme `G` over `Spec (CommRingCat.of k)`, the proposition asserts
`IsConnectedReductive G → IsConnectedReductive G_K`, where

```lean
G_K = (GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G
```

Here the displayed equality specifies notation in this documentation.
`GroupScheme.baseChange`, defined in
`Langlands.AbelianScheme.GroupScheme`, is `(Over.pullback f).mapGrp`.
Thus `G_K` is the actual pullback group object with its induced group law.
The algebra map between fields is injective, so this quantification describes
an arbitrary field extension. There is no assumption on characteristic,
perfection, algebraicity, separability, degree, splitness or dimension. The
trivial group and zero-dimensional cases are included.

## Original sources and errata

- J. S. Milne, *Algebraic Groups* (2017), registered source
  `milne-2017-algebraic-groups`: Proposition 19.13, printed p.400
  (one-based PDF p.416), states that reductivity is equivalent before and
  after an arbitrary extension of the ground field. This declaration takes
  its forward implication. Paragraphs 6.45–6.46, printed p.135
  (PDF p.151), give the representation-theoretic unipotence condition and
  the geometric-unipotent-radical definition of reductivity. The beginning
  of §19.b, printed p.400, recalls that definition.
- B. Conrad, *Reductive group schemes* (2014), registered source
  `conrad-2014-reductive-group-schemes`: Definition 3.1.1 and the following
  discussion, printed/PDF p.81, explain that unipotent radicals commute
  with extension of algebraically closed fields and that connected
  finite-type group schemes over a field are geometrically connected.
  Exercise 3.4.1, printed/PDF p.104, supplies the indicated radical
  base-extension argument.
- Milne's official errata, registered source
  `milne-2017-algebraic-groups-errata-2026-11-02`, retained HTML snapshot
  dated 2026-11-02, was consulted. Its list has no correction to 6.45,
  6.46 or Proposition 19.13.

## Correspondence with the existing predicate

The declaration imports `Langlands.GroupScheme.Reductive.Basic` and uses
its `IsConnectedReductive` unchanged. Its four fields require smoothness,
affineness of the structure morphism, connectedness of the underlying
scheme, and `HasTrivialUnipotentRadical` after base change along
`toAlgebraicClosure k`. Smoothness and affineness put the group in the
finite-type affine setting of the cited algebraic-group result.

`HasTrivialUnipotentRadical` tests every smooth connected unipotent normal
closed subgroup. Its conclusion is equality of the subgroup functor's
range with the bottom subgroup functor on all test schemes. This expresses
triviality of the geometric unipotent radical, rather than only triviality
of its rational points. `IsUnipotent` uses fixed vectors in finite
dimensional matrix representations, matching Milne 6.45. The statement
does not replace the geometric condition by the unipotent radical over
`k`, which would give the different pseudo-reductive condition over
imperfect fields.

The input tests the group over `AlgebraicClosure k`; the conclusion tests
`G_K` over `AlgebraicClosure K`. These chosen closures are generally
different types. To apply the original result to this presentation, a
proof can choose a `k`-embedding of `AlgebraicClosure k` into
`AlgebraicClosure K` compatible with `algebraMap k K`. Pullback-composition
isomorphisms then compare the two iterated base changes over the larger
closure. Radical invariance under algebraically closed extension gives
the required triviality there. Smoothness and affineness are preserved by
base change; geometric connectedness supplies connectedness after the
arbitrary extension. These comparisons and invariance results are proof
obligations, not hypotheses of this proposition or results proved in this
module.

This is a direct statement of the forward direction of Milne 19.13 in the
Library's existing geometric predicates. It introduces no new definition
of reductivity and no maximal-torus or parabolic theorem.
