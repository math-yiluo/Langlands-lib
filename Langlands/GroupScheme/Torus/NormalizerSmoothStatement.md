# Statement: smooth closed normalizers of arbitrary field tori

`Langlands.GroupScheme.TorusNormalizerSmoothClosedStatement.{u}` states that,
over every field `k : Type u`, the all-test normalizer of every closed torus in
every smooth affine group scheme over `Spec k` has a smooth closed
representative. It is a `Prop`-valued definition. This file provides the
statement for a subsequent proof task.

## Exact formulation

The ambient object is
`G : GroupScheme (Spec (CommRingCat.of k))`, with precisely the typeclass
assumptions `[Smooth G.X.hom]` and `[IsAffineHom G.X.hom]`. The torus is a
commutative group scheme `T` and a homomorphism `i : T.toGrp ⟶ G`, subject to
`IsTorus T.toGrp` and `IsClosedSubgroup i`. The conclusion is

```lean
(torusNormalizer i).HasSmoothClosedRepresentative
```

The imported predicate
`SubgroupFunctor.HasSmoothClosedRepresentative` is defined in
`Langlands.GroupScheme.Rational.TorusNormalizerStatement`. It asserts the
existence of an actual group scheme `H` and homomorphism `j : H ⟶ G` with
`IsClosedSubgroup j`, `Smooth H.X.hom`, and
`(torusNormalizer i).IsRepresentedBy j`.
Here `IsClosedSubgroup` means that the underlying morphism is a closed
immersion. The imported `IsRepresentedBy` requires a monomorphism on underlying
schemes over the base and the equality
`SubgroupFunctor.range j = torusNormalizer i`.
This is equality of subgroup functors on every scheme test.

No connectedness or reductivity of `G`, splitness or maximality of `T`,
perfectness of `k`, or characteristic assumption occurs.

## Original source and locators

The source is James S. Milne, *Algebraic Groups: The Theory of Group Schemes
of Finite Type over a Field*, Cambridge Studies in Advanced Mathematics 170,
Cambridge University Press, 2017, registered as
`milne-2017-algebraic-groups`. The retained original is
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
For this copy, the one-based PDF page number is the printed page number plus 16.
The relevant original passages are:

- Proposition 1.83, printed p.31, PDF p.47: for an algebraic subgroup `H` of
  `G`, the normalizer `N_G(H)` is an algebraic subgroup representing, on every
  `k`-algebra `R`, the elements `g` that preserve `H(R')` by conjugation for
  every `R`-algebra `R'`. Its proof establishes representation by a closed
  subscheme of `G`.
- Corollary 13.10, printed p.257, PDF p.273: if `H` is a subgroup variety of
  multiplicative type in a group variety `G`, both `C_G(H)` and `N_G(H)` are
  smooth. Only the normalizer assertion is used here.
- Definition 1.1, printed p.6, PDF p.22, and Proposition 1.26 with the
  terminology immediately following it, printed p.13, PDF p.29: an algebraic
  group is a finite-type group scheme over the field, and a group variety
  is precisely a smooth algebraic group. Connectedness is not part of this
  convention.
- Definitions 12.14 and 12.17, printed p.236, PDF p.252: a torus becomes a
  finite product of copies of the multiplicative group after a field
  extension, and a group of multiplicative type becomes diagonalizable
  after a field extension. In particular, tori are smooth connected
  groups of multiplicative type.

The official author errata, retained as
`milne-2017-algebraic-groups-errata-2026-11-02` from
<https://jmilne.org/math/Books/iag2errata.html>, were also read.
That snapshot contains no correction to Proposition 1.83, Corollary 13.10,
or the cited definitions and terminology.

## Specialization and provenance

This is a derived formulation of the cited source results in the published
group-scheme and subgroup-functor interfaces.

A smooth affine group scheme over a field is of finite type: smoothness
gives local finite presentation, and affineness gives quasi-compactness.
Thus the ambient `G` is an algebraic group in Milne's sense and, by its
smoothness, a group variety. Since `i` is a closed immersion, it identifies
`T` with a closed algebraic subgroup of `G`.

The published `IsTorus` in `Langlands.GroupScheme.Torus.Lattice` says that
`T.toGrp` becomes a split torus after some field extension. A field extension
gives an fpqc cover of spectra; smoothness and finite type descend along
that cover. A split torus is diagonalizable, so this is exactly a smooth
subgroup variety of multiplicative type as required in Corollary 13.10.
Consequently Proposition 1.83 supplies a closed normalizer subgroup, and
Corollary 13.10 supplies its smoothness.

The passage from algebra tests to all scheme tests is part of the
formulation. The published `torusNormalizer i` is
`(SubgroupFunctor.range i).normalizer`. At a test scheme `U`, membership
requires conjugation by a point `g` and by `g`'s inverse to preserve the torus
points after every refinement `V ⟶ U`. The two inclusions express equality
of the conjugated subgroup. For affine `U = Spec R` and affine
`V = Spec R'`, these are exactly Milne's conditions for every `R`-algebra
`R'`.

Arbitrary `V` are covered by affine open subschemes. Factoring a map through
the closed immersion `i` is local on its source, and its factorizations are
unique because `i` is a monomorphism. Therefore the affine conditions glue
to the conditions for every `V`. Covering `U` by affine opens likewise
extends the identification to every `U`; the representing closed subgroup
and its inclusion satisfy the required equality of all-test subgroup
functors. This explains the source correspondence, rather than asserting
a Lean proof of it in this statement module.

## Relation to the existing split statement

`Langlands.GroupScheme.TorusNormalizerRepresentableStatement` in
`Langlands.GroupScheme.Rational.TorusNormalizerStatement` assumes
`IsConnectedReductive G` and `IsSplitSubtorus i`, and asks for both normalizer
and centralizer representatives. The present statement asks only for the
normalizer, allows an arbitrary torus, and assumes only smoothness and
affineness of `G`. In particular it applies to nonsplit maximal tori in
smooth connected affine groups without reductivity, as well as to
nonmaximal tori and disconnected ambient groups.

The existing split statement and its proof are unchanged. This module
imports its representative predicate instead of defining another one.
