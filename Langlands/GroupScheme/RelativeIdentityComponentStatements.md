# Smooth relative identity-component structure targets

This file declares three proposition-valued targets for actual smooth group
schemes over an arbitrary base. It uses the published
`IsRelativeIdentityComponent` predicate, whose all-test factorization condition
is the residue-fibre image criterion of SGA 3, Exposé VI_B, Definition 3.1.
These are statements awaiting proofs.

## Exact assertions

All names below are in `Langlands.GroupScheme.RelativeIdentityComponent`.
The base schemes, group schemes and test schemes share an arbitrary universe
`u`.

`SmoothExistenceStatement` quantifies over every scheme `S` and actual group
scheme `G` over `S`. If `G.X.hom` is smooth, there exist an actual group scheme
`H` and homomorphism `i : H → G` satisfying
`IsRelativeIdentityComponent G i`. In particular, `i` is an open immersion and,
on every test scheme, factorization through `i` is equivalent to the image in
each residue fibre lying in its identity connected component. The statement
also requires `H.X.hom` to be smooth and geometrically connected.

`SmoothNormalityStatement` concerns every supplied homomorphism `i : H → G`
representing this relative component, when `G` is smooth. It asserts
`(SubgroupFunctor.range i).IsNormal`. Thus, for every test scheme `T` over `S`,
every `g : T → G.X`, and every `x : T → G.X` factoring through `i`, the point
`g * x * g⁻¹` also factors through `i`. This is normality of the actual subgroup
on all test schemes, including nonreduced tests.

`SmoothBaseChangeStatement` concerns every such supplied representation and
every morphism `b : S' → S`. The actual pullback homomorphism
`(GroupScheme.baseChange b).map i` must satisfy
`IsRelativeIdentityComponent` for `(GroupScheme.baseChange b).obj G`.
There is no flatness, smoothness, surjectivity or reducedness restriction on
`b` or `S'`.

`SmoothStructureStatement` is the conjunction of these three targets in the
same universe. None of the existence, normality or base-change conclusions is
provided as an extra premise. In the latter two assertions a representation
is supplied because the assertions specify the properties of every such
representation.

## Original source and internal consequences

J.-E. Bertin, SGA 3, Exposé VI_B, Gille–Polo recomposed edition of
13 October 2024:

- Definition 3.1, Proposition 3.3 and special case 3.4, PDF pp. 17–18,
  printed pp. 347–348 (original margin pp. 341–342), give the all-test
  criterion, its compatibility with arbitrary base change, and representation
  by the union of the fibre identity components when this union is open.
- Theorem 3.10 and its proof, PDF pp. 20–21, printed pp. 350–351
  (original margin pp. 345–346), give an open smooth subgroup representing
  this functor when the ambient group is smooth at its unit section.
  `SmoothExistenceStatement` uses the global smoothness special case.

Registered source: `sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
The cited passages were read in the retained original. The complete official
one-page Tome I errata of 13 October 2024 was also read:
`sga3-tome1-errata-gille-polo-2024`, SHA-256
`e17b90eac75b25f53b5a6f7be84450b71c2f0d7df98f5c9f4ad4cb8e9038cea7`.
It contains no change to the cited passages.

The geometric connectedness clause is the fibre consequence of representation
and arbitrary base change: a fibre is the identity connected component, and
after any extension of its residue field it is again that component.
The explanation of Proposition 3.3 explicitly uses geometric connectedness of
the field identity component and its rational identity point.

Normality is an internal consequence of the same component construction, rather
than a separately numbered theorem claimed from these pages. On each geometric
fibre, conjugation preserves the identity component. Applying this fact to
the conjugation morphism and the fibre-image criterion gives the assertion
on every test scheme. The future proof must establish this scheme-level
argument and its all-test conclusion. The statement does not replace it by
normality only on rational or geometric points.

The base-change target expresses Proposition 3.3 using the actual pullback
homomorphism and its all-test representation predicate. Open immersion
stability under pullback and uniqueness of a represented subfunctor supply
the representation formulation.

## Scope

There is no affineness, separation, noetherian, quasi-compactness, field,
connectedness or perfectness premise on the base or on the ambient group.
Global smoothness is the one ambient morphism hypothesis. The statement
does not assert that the component inclusion is closed or affine, or that
the component is affine over a general base.

Affineness of a smooth relative component over a DVR is a separate target.
These declarations also do not construct component quotients, integral
models, smoothenings, dilatations, gluing data or Bruhat–Tits models.
