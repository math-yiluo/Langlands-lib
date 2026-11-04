# Central multiplicative quotient and Borel descent

Authors: Worker 1369 (draft); Worker 1499 (review, Markdown revision).

This is a derived statement, not a proof.
`CentralMultiplicativeQuotientBorelStatement` is a proposition at arbitrary
universe `u`. It says that a central closed copy of `Gm` inside a Borel can be
quotiented out. The quotient stays smooth, connected and affine, its Lie
dimension drops strictly, and the Borel descends with the exact inverse image
on every test scheme.

## Hypotheses

- `k : Type u` is an algebraically closed field. `G` is a group scheme over
  `Spec k` whose structure morphism is smooth and affine, and whose underlying
  topological space is connected.
- `i : B ⟶ G` is an actual group-scheme homomorphism satisfying the published
  `IsBorelSubgroup` (in `Absolute/Borel.lean`). This means `i` is a closed
  immersion and `B` is smooth, connected and solvable. It is also maximal: if
  `i` factors as `f ≫ i'` through another smooth, connected, solvable closed
  subgroup `i'`, then `f` is an isomorphism.
- `z : Gm ⟶ G` is a homomorphism from the multiplicative group over `Spec k`
  with `IsClosedSubgroup z`, which says the underlying morphism of schemes is a
  closed immersion. It also satisfies `SubgroupFunctor.range z ≤ center G`.
  Here `range z` is the subgroup functor of points that factor through `z`.
  The published `center G` is the all-test scheme-theoretic centre: a point
  over `T` is central when each restriction along any `T' ⟶ T` commutes with
  every point of `G` over `T'`.
- `zB : Gm ⟶ B` is an actual factor with `zB ≫ i = z`, recording that this
  copy of `Gm` lies in the given Borel.

## Conclusions

The statement asserts that there exist a group scheme `Q` and a homomorphism
`q : G ⟶ Q` with the following properties.

- `Q.X.hom` is affine (the witness `hAffQ`, used as the instance that makes
  `Lie.dimension Q` meaningful) and smooth. The underlying space of `Q` is
  connected, and the underlying morphism of `q` is smooth.
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q` holds. This
  existing predicate says the underlying morphism of `q` is flat, surjective
  and locally of finite presentation, and that the range of the actual
  scheme-kernel inclusion `kernelι q` equals `range z` on every test scheme.
  It describes a represented sheaf quotient. It does not assert that
  `G(T) → Q(T)` is surjective for every test scheme `T`.
- `Lie.dimension Q < Lie.dimension G`. The published `Lie.dimension` (in
  `Lie/DimensionInduction.lean`) is `Module.finrank k` of the actual additive
  kernel of reduction `G(k[ε]) → G(k)`. A proof must establish this strict
  drop for the constructed quotient. The statement assumes no quotient
  dimension formula.

It also asserts that there exist a group scheme `BQ` and homomorphisms
`iQ : BQ ⟶ Q` and `qB : B ⟶ BQ` with the following properties.

- `IsBorelSubgroup iQ` holds, and `i ≫ q = qB ≫ iQ`.
- The underlying morphism of `qB` is smooth, and
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range zB) qB` holds.
- `(SubgroupFunctor.range iQ).comap q = SubgroupFunctor.range i`. The
  published `SubgroupFunctor.comap` (in `Dynamic/Functoriality.lean`) takes
  the points `x : T ⟶ G` with `x ≫ q` in the given subgroup functor. So, for
  every test scheme `T` over `Spec k`, a point of `G` lies in the range of
  `i` exactly when its image in `Q` lies in the range of `iQ`. This is an
  inverse-image equality. It does not assert that `B(T) → BQ(T)` is
  surjective for arbitrary `T`.

The conclusions are explicit data, not normalizer facts. The statement neither
assumes nor concludes `BorelNormalizerStatement` or
`ParabolicSelfNormalizerStatement`.

Given `IsClosedSubgroup z` and affineness of `Q`, the published lemma
`RelativeRoot.IsFppfQuotient.gm_induction_properties` (in
`Absolute/BorelNormalizerCentralQuotient.lean`) already derives smoothness of
`q`, smoothness and connectedness of `Q`, and the strict Lie dimension drop
from the quotient predicate. These conclusions are still listed explicitly, as
the task requests. The substantive content is that `Q`, `q`, `BQ`, `iQ` and
`qB` exist, together with the Borel and inverse-image clauses.

## Intended consumer

This statement supplies the inputs of the published theorem
`normalizer_borelRange_eq_of_fppf_gm_quotient` in
`Absolute/BorelNormalizerCentralQuotient.lean`. That theorem takes an affine
`q` with `IsFppfQuotient (range z) q`, a Borel `iQ` of `Q`, and the
inverse-image equality as its hypothesis `hpre`. It then reduces the Borel
normalizer equality for `G` to the induction hypothesis for `Q`, which has
smaller Lie dimension. This is the central torus branch of the dimension
induction in the Borel normalizer proof. General central quotients by
arbitrary group schemes, and descent of other kinds of subgroups, are outside
its scope.

## Provenance

This statement is derived; it is not stated in this form in the literature.
The registered source is J. S. Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. PDF page
numbers equal printed page numbers plus 16. Write `Z` for the image of `z`.
Centrality makes `Z` normal. The passages behind each clause are:

- Proposition 5.18, printed p.103/PDF p.119, and Proposition 5.29, printed
  p.105/PDF p.121: a normal algebraic subgroup of an affine algebraic group is
  the kernel of a quotient map to an affine algebraic group `G/Z`.
- Proposition 5.25 and Corollary 5.26, printed p.105/PDF p.121: the quotient
  map is faithfully flat, and `G/Z` is smooth when `G` is. `G/Z` is connected
  as the image of the connected `G`.
- Proposition 7.15 and Remark 7.16(a), printed pp.142–143/PDF pp.158–159:
  the quotient projection by a smooth subgroup is smooth, here `G → G/Z`
  and `B → B/Z`. In the smoothness sentence of 7.15 the prose reverses the
  arrow; the displayed cartesian square and the stated specialization
  `G → G/H` fix the direction used here.
- Proposition 5.23, printed p.104/PDF p.120, and Proposition 1.37, printed
  p.18/PDF p.34: `dim G/Z = dim G − 1`, and for smooth groups the tangent
  dimension equals the dimension. The dual-number kernel is the tangent space
  at the identity, so `Lie.dimension Q = dim G − 1 < Lie.dimension G`.
- Theorem 5.13, printed p.101/PDF p.117; Theorem 5.34, printed p.107/PDF
  p.123; and Theorem 5.39, printed p.108/PDF p.124. Since `Z ⊂ B`, the
  composite `B → G → G/Z` has kernel `Z` and factors through `B/Z`. The
  induced homomorphism `B/Z → G/Z` has trivial kernel, so it is a closed
  immersion `iQ` onto `q(B)`. This gives the commuting square.
- Proposition 17.20, printed pp.357–358/PDF pp.373–374: the image of a Borel
  subgroup under a quotient map of connected group varieties is a Borel
  subgroup, so `iQ` is Borel.
- Corollary 5.27, printed p.105/PDF p.121: `G` is a `Z`-torsor over `G/Z`,
  and `B` is a `Z`-torsor over `B/Z`. The pullback `G ×_{G/Z} B/Z → B/Z` is
  then a `Z`-torsor, and `B → G ×_{G/Z} B/Z` is a `Z`-equivariant morphism of
  `Z`-torsors over `B/Z`. It is therefore an isomorphism of schemes. A point
  `x : T ⟶ G` whose image in `Q` factors through `iQ` therefore factors
  through `i`; the converse follows from the commuting square. Because the
  isomorphism is of schemes, this gives the inverse-image equality on every
  test scheme, not only on affine ones. This all-test equality is our
  derivation; Milne does not state it in this form.
- The central quotient branch in the proof of Theorem 17.48, printed
  p.367/PDF p.383, motivates this prerequisite. There `S ⊂ Z(G)` and the
  argument passes by induction to `G/S`.

All these passages were read directly, as was the complete registered author's
errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`. It
contains no correction to these results.

The Lean formulation replaces Milne's `G/Z` and `B/Z` by actual group schemes
`Q` and `BQ`, with homomorphisms characterized by the published
`IsFppfQuotient` predicate. A flat, surjective homomorphism with the stated
kernel is a quotient map in Milne's sense, so by Theorem 5.13 it is unique up
to unique isomorphism. Local finite presentation holds automatically for
homomorphisms of algebraic groups over a field.
