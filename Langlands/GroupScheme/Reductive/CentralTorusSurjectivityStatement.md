# Central torus and derived subgroup cover a connected reductive group

Worker 1044 (draft); checked and revised by Worker 1383.

`Langlands.GroupScheme.ReductiveCentralTorusSurjectivityStatement` is a
universe-polymorphic proposition definition. This module defines the
proposition and contains no proof of it. It isolates the deep structure-theory
part of the published `ReductiveCentralDerivedProductStatement` (module
`Langlands.GroupScheme.Reductive.CentralDerivedProductStatement`). The two soft
parts of that target are excluded: constructing a derived-subgroup inclusion,
and passing from surjectivity to epimorphy.

## Quantifiers and predicates

For every universe `u`, the statement quantifies over:

- every `k : Type u` with a `Field k` instance;
- every pair of actual group schemes
  `G D : GroupScheme (Spec (CommRingCat.of k))` (group objects in
  `Over (Spec k)`);
- every group-scheme homomorphism `d : D ⟶ G`.

It has two premises:

- `IsConnectedReductive G`, the published geometric reductivity predicate. It
  requires `G` to be smooth, affine and connected over `k`, and its unipotent
  radical to be trivial after base change to an algebraic closure. It is not the
  weaker pseudo-reductive condition over `k`.
- `IsDerivedSubgroup d`, the published derived-subgroup predicate. It requires
  `d` to be a closed immersion whose full range functor equals
  `derivedSubgroup G`, the scheme-theoretic derived subgroup. It is not the
  abstract commutator subgroup of `G(k)`.

The conclusion chooses a commutative group scheme `Z` over the same `Spec k`
and a homomorphism `i : Z.toGrp ⟶ G`. They may depend on all earlier data,
including `d`. The conjuncts are as follows:

- `IsAffineHom Z.toGrp.X.hom` and `LocallyOfFiniteType Z.toGrp.X.hom`: the
  structure morphism of `Z` is affine and locally of finite type, so `Z` has
  finite type over `k`.
- `IsTorus Z.toGrp`: the published torus predicate. Some field `K : Type u`
  with `Algebra k K` makes the base change of `Z` to `Spec K` isomorphic to a
  finite product of copies of the multiplicative group. Rank zero is allowed.
- `IsClosedSubgroup i`: the underlying scheme morphism of `i` is a closed
  immersion.
- `IsCentral i`: functorial centrality. Every image point over any scheme `T`
  over `Spec k`, after restriction along any `T' ⟶ T`, commutes with every
  `G`-point over `T'`.
- `Function.Surjective (subgroupProductMap i d).left`: the underlying map of
  topological spaces of the actual published multiplication morphism
  `subgroupProductMap i d : Z.toGrp.X ⊗ D.X ⟶ G.X` is surjective. Here `⊗`
  is the fibre product over `Spec k`, and on test points the map sends `(z, x)`
  to `i(z) * d(x)`. The construction is imported unchanged from
  `Langlands.GroupScheme.Rational.ProductDetection`.

The statement has no perfectness, characteristic, splitting,
algebraic-closedness, local-field or character hypotheses. Only a central torus
is chosen. Nothing is claimed about the whole centre, and no canonical radical
is defined.

## Why quantify over every derived inclusion

The statement fixes `d` before choosing `Z`, rather than choosing `D` and `d`.
So it can be combined with any derived inclusion, for example one built by a
separate proof of `DerivedSubgroupRepresentabilityStatement`. This choice
loses no generality. Two inclusions with `IsDerivedSubgroup` have the same
range functor, so they are isomorphic as closed subgroups of `G`, and the two
product maps then have the same image.

## Relation to the published target

Surjectivity on underlying points is weaker than the faithfully flat quotient
map in the source, and it does not by itself give epimorphy in
`Over (Spec k)`. A connected reductive `G` is smooth over a field, so it is
reduced. For a map onto a reduced scheme, surjectivity on points makes the
structure-sheaf maps on opens injective. Hence two morphisms out of `G.X` that
agree after `subgroupProductMap i d` agree on points and on functions. That
deduction is a separate soft lemma, and so is the construction of a derived
inclusion `d`. Together with them, this statement yields
`ReductiveCentralDerivedProductStatement`.

## Original source and derivation

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, at
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
Printed page `p` is PDF page `p + 16`.

The statement packages these passages; no single proposition in the source
states it verbatim:

1. Milne's reductive groups are smooth, connected algebraic groups whose
   geometric unipotent radical is trivial (6.46, recalled on printed p.400 /
   PDF p.416). This matches `IsConnectedReductive`.
2. Corollary 17.62 (printed pp.372–373 / PDF pp.388–389) holds for a
   reductive group `G` over any field `k`. Part (b) says
   `R(G) = Z(G)_t`, the largest subtorus of the centre. So the radical
   `R(G)` is a torus contained in the centre, that is, a central torus in the
   sense of Definition 12.44 (printed p.245 / PDF p.261). Part (d) says that
   `G/R(G)` is semisimple. Neither part assumes that `k` is perfect.
3. Corollary 21.50 (printed p.440 / PDF p.456) says that every semisimple
   algebraic group is perfect. Hence `G/R(G)` is perfect.
4. Proposition 12.46(b) (statement on printed p.245 / PDF p.261, proof on
   printed p.246 / PDF p.262) applies to a central torus `T` in a connected
   group variety `G` with `G/T` perfect. It says that the sequence
   `e → T ∩ D(G) → T × D(G) → G → e` is exact, and that the multiplication
   map `T × D(G) → G` is a homomorphism with image `G`. Here `T × D(G)` is
   the fibre product over `k`, which matches `Z.toGrp.X ⊗ D.X`.
5. By Definition 1.61 (printed p.24 / PDF p.40), exactness of a sequence
   ending in `G → e` includes faithful flatness of the last map. Definition
   5.5 (printed p.99 / PDF p.115) calls such a homomorphism a quotient map
   and notes that it is flat and surjective. Milne works with max specs
   (Appendix A introduction, printed p.566 / PDF p.582). By the dictionary
   in A.22 (printed p.571 / PDF p.587), a regular map of algebraic schemes
   over `k` is surjective if and only if it is surjective on closed points.
   So Milne's surjectivity is surjectivity on all points of the
   corresponding scheme, which is what `Function.Surjective (...).left`
   states. The proof of 12.46 first reduces to algebraically closed `k`.
   This is valid because Definition 1.61 notes that exact sequences stay
   exact under extension of the base field.
6. Proposition 21.61 (printed p.443 / PDF p.459) states the resulting
   almost-direct-product decomposition for connected group varieties over a
   field that need not be perfect. Its proof of (b) ⇒ (c) refers to "the
   same argument as in the proof of Proposition 21.60". That proof (printed
   p.442 / PDF p.458) cites Proposition 19.2 for semisimplicity of
   `G/R(G)`, but 19.2 (printed p.398 / PDF p.414) assumes `k` perfect. For
   a reductive `G` over an arbitrary field, Corollary 17.62(b),(d) supplies
   the same two facts, as in steps 2–4 above. The route above therefore
   cites 17.62 directly and does not depend on 19.2.
7. Definition 12.14 (printed p.236 / PDF p.252) gives the meaning of torus.
   Definition 6.16 and Proposition 6.18 (printed p.129 / PDF p.145) give the
   derived group that the published `IsDerivedSubgroup` interface describes.

The choice `Z = R(G)` with its inclusion therefore satisfies the conclusion,
for any `d` with `IsDerivedSubgroup d`. Surjectivity, rather than faithful
flatness, is requested only because it is all the published target needs.

## Errata

The official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`,
SHA256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`, at
`/home/taskhub/pilot/literature/J. S. Milne - Errata for Algebraic Groups (2017), HTML snapshot 2026-11-02.html`,
has corrections in Chapters 12 and 21: 12.41, 12.57, and a rewritten proof of
21.51, among others. The route above uses 1.61, 5.5, 12.14, 12.44, 12.46,
17.62(b),(d), 21.50, 21.60(b) ⇒ (c), 21.61 and A.22. It does not use the
proof of 21.51 or 12.41; 12.41 enters only the proof of 17.62(e), which the
route does not use. No displayed erratum changes the passages used. The
Appendix A erratum to footnote 3 on printed p.570 does not concern A.22.

## Proof boundary

Defining and compiling this proposition proves nothing. A proof has to build
the radical as an actual closed central torus over an arbitrary field, show
that the quotient is semisimple and therefore perfect, and derive the
surjectivity of the actual `subgroupProductMap`. The published Library
currently contains no proof of these facts.
