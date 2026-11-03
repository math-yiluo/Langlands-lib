# Central torus and derived subgroup generation

Worker 1350, using the interface and original-source route supplied by Worker 1306.

`Langlands.GroupScheme.ReductiveCentralDerivedProductStatement` is a
universe-polymorphic proposition definition. It states a structural existence
result for actual connected reductive group schemes over arbitrary fields.
This module defines the proposition; it contains no proof of that proposition.
The source derivation below explains its mathematical provenance and the
obligations of a later proof.

## Quantifiers and predicates

For every universe `u`, the statement quantifies over every `k : Type u` with a
`Field k` instance and every actual `G : GroupScheme (Spec (CommRingCat.of k))`.
Here `GroupScheme S` is the category of group objects in `Over S`. The sole
premise is the published `IsConnectedReductive G`. It requires smoothness,
affineness and connectedness of `G`, and triviality of the unipotent radical
after base change to an algebraic closure. Triviality tests all smooth connected
unipotent normal closed subgroups of that geometric group. It is the geometric
reductive condition, not the weaker condition on the unipotent radical over `k`
alone. Smoothness gives local finite presentation, and affineness gives
quasi-compactness, so the field group is of finite type.

The conclusion existentially chooses a commutative group scheme `Z`, a group
scheme `D`, and group-scheme homomorphisms `i : Z.toGrp ⟶ G` and `d : D ⟶ G`,
all over the same `Spec k`. The witnesses can depend on `k`, its field
structure, `G` and its reductivity premise. The statement does not define a
canonical radical. Its seven conjuncts have these meanings:

- `IsAffineHom Z.toGrp.X.hom` says that the structure morphism of `Z` is affine.
- `LocallyOfFiniteType Z.toGrp.X.hom` says that it is locally of finite type.
  Together with affineness this gives finite type over `k`.
- `IsTorus Z.toGrp` is the published torus predicate: there exist a field
  `K : Type u`, a field structure on `K` and an `Algebra k K` structure such
  that the actual base change to `Spec K` is isomorphic to a finite product of
  copies of the multiplicative group scheme. Both the splitting field and
  the finite index type are in the same universe `u`. Rank zero is allowed.
- `IsClosedSubgroup i` requires the underlying scheme morphism of `i` to be
  a closed immersion, so `Z` is an actual closed subgroup.
- `IsCentral i` requires every image point over every test scheme `T` over
  `Spec k` to belong to the published centre functor. Such a point, restricted
  along any `T' ⟶ T`, must commute with every `G`-point over `T'`. This includes
  non-affine and nonreduced test schemes.
- `IsDerivedSubgroup d` requires a closed immersion and equality of its full
  range functor with `derivedSubgroup G`. The latter is the intersection of
  the ranges of all actual closed subgroup homomorphisms containing all
  commutators on every test scheme. This describes the scheme-theoretic
  derived subgroup, not the abstract commutator subgroup of `G(k)`.
- `Epi (subgroupProductMap i d)` requires epimorphy of the actual underlying
  multiplication morphism described next.

There are no perfectness, characteristic, splitting, algebraic-closedness,
local-field or character hypotheses.

## The actual map and its epimorphism condition

The module imports `subgroupProductMap` unchanged from
`Langlands.GroupScheme.Rational.ProductDetection`. If `S = Spec k`, its type is

```lean
subgroupProductMap i d : Z.toGrp.X ⊗ D.X ⟶ G.X
```

The tensor here is the product of schemes over `S`, namely the fibre product.
The map multiplies the images of its two projections, sending `(z, x)` to
`i(z) * d(x)` on test points. Its construction does not need centrality;
centrality is a separate conjunct of this structural statement.

`Epi` is taken in `Over (Spec k)`. Explicitly, for every scheme `Y` over `k`
and every pair of scheme morphisms `a, b : G.X ⟶ Y` over `k`, equality
`subgroupProductMap i d ≫ a = subgroupProductMap i d ≫ b` implies `a = b`.
The test morphisms need not preserve a group law, and `Y` need not be a group
scheme or of finite type. Thus the target is not merely epimorphy in the
group-scheme category. It asserts no surjectivity on `k`-points or on points
over every test scheme.

## Original source and derivation

The original is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
It is retained at
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
Printed page `p` is PDF page `p + 16`.

The statement is a derived packaging of these passages, rather than a verbatim
translation of a single proposition:

1. Milne 6.46, printed p.135 / PDF p.151, defines reductivity by the trivial
   geometric unipotent radical. Proposition 21.61, printed p.443 / PDF p.459,
   applies to a connected group variety over a field that need not be perfect.
   Its implication (a) to (b) gives a torus as geometric radical; in (b) to (c),
   it obtains that the radical over `k` is a torus and explicitly reuses the
   argument of 21.60.
2. The proof of 21.60(b) to (c), printed p.442 / PDF p.458, takes
   `T = R(G)`, a central torus, and uses that `G/T` is semisimple.
   Corollary 21.50, printed p.440 / PDF p.456, makes that quotient perfect.
   These are the steps reused by 21.61 for arbitrary fields; the perfect-field
   premise of 21.60 is not imposed on the present statement.
3. Proposition 12.46(b) and its proof, printed pp.245–246 / PDF pp.261–262,
   give an exact sequence from `T × D(G)` onto `G` when `T` is central
   and `G/T` is perfect. The proof identifies its arrow as multiplication
   and its image as all of `G`. This supplies the chosen torus, actual
   derived subgroup and multiplication map. The finite intersection in
   12.46(a) is stronger than anything required by the present target.
4. Definition 12.14, printed p.236 / PDF p.252, supplies the torus meaning.
   Definition 6.16 and Proposition 6.18, printed p.129 / PDF p.145, identify
   the derived group with the smallest algebraic subgroup containing the
   commutator morphism for an affine or smooth group. Passing to full range
   functors on schemes gives the published `IsDerivedSubgroup` interface:
   factorization through a closed subgroup can be checked on affine opens,
   and factorization of the commutator morphism is equivalent to containment
   of all test-scheme commutators. The witnesses are actual finite-type
   subgroup schemes and their inclusion morphisms.
5. Definition 5.5 and Proposition 5.7, printed p.99 / PDF p.115, and
   Proposition 5.43, printed p.109 / PDF p.125, explain faithfully flat
   quotient maps and lifting after faithfully flat extension. Aside 5.44,
   printed pp.109–110 / PDF pp.125–126, distinguishes epimorphisms among
   algebraic groups from epimorphisms among algebraic schemes. The exact
   multiplication sequence in 12.46 gives a faithfully flat quotient map,
   a stronger condition than the `Epi` requested here.

The passage from that finite-type quotient to cancellation against *all*
schemes over `k` is an internal extension of the categorical presentation.
For two maps out of `G` that agree after the quotient, surjectivity first
makes their underlying continuous maps agree. On the common inverse image of
each affine open of the target, injectivity of the structure-sheaf map of
the faithfully flat quotient (the condition in 5.43(c), restricted to opens)
makes their maps on functions agree. Thus the scheme morphisms agree.
This argument allows an arbitrary target scheme and gives cancellation in
`Over (Spec k)`; it does not replace the quotient map by rational-point
generation. The same-universe splitting convention of `IsTorus` is respected
by taking an algebraic splitting extension in universe `u`.

## Errata and proof boundary

The official author errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read at
`/home/taskhub/pilot/literature/J. S. Milne - Errata for Algebraic Groups (2017), HTML snapshot 2026-11-02.html`.
The displayed Chapter 12 corrections concern both 12.41 and 12.57.
Chapter 21 has several corrections, including a rewritten proof of 21.51.
The route above uses 21.50 and 21.60(b) to (c), not the 21.51 proof used in
another implication of 21.60. No displayed erratum changes 12.46 or 21.61.
The Chapter 6 caution about 6.19(c)–(e) occurs inside an HTML comment and is
not a displayed correction; that caution is not used to change the target.

Only a central torus is chosen. No assertion that the entire centre of a
reductive group is smooth is made. The source argument, its comparison with
the published subgroup functors, the witness construction, and epimorphism of
the exact imported map remain obligations for a separate Lean proof of
`ReductiveCentralDerivedProductStatement`. Defining and compiling this
`Prop`-valued statement does not discharge those obligations.
