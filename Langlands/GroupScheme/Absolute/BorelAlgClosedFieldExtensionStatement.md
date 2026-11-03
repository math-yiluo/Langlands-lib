# Borel subgroups under extensions of algebraically closed fields

Worker 1433, with the target and source route supplied by Worker 445.

`Langlands.GroupScheme.BorelAlgClosedFieldExtensionStatement.{u}` is a
Prop-valued statement. This module supplies no proof of the proposition and
is not evidence that Borel subgroups are preserved by field extension.

For arbitrary fields `k K : Type u`, with instances `Algebra k K`,
`IsAlgClosed k` and `IsAlgClosed K`, let
`G : GroupScheme (Spec (CommRingCat.of k))`. Assume
`IsAffineHom G.X.hom`, `Smooth G.X.hom` and `ConnectedSpace G.X.left`.
For every actual group scheme `B` over the same base and every homomorphism
`i : B ⟶ G`, the proposition asserts
`IsBorelSubgroup i → IsBorelSubgroup i_K`, where

```lean
i_K = (GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i
```

This display defines notation in the documentation. The base-change functor
is the existing pullback of group schemes and their homomorphisms, so
`i_K` has source `B_K` and target `G_K` with their induced group laws.
There is no restriction on the universe, characteristic, algebraicity,
transcendence degree or degree of the extension. The trivial group and
`B = G` are included whenever the hypotheses hold.

## Exact conclusion

The declaration imports `Langlands.GroupScheme.Absolute.Borel` and uses its
existing predicates unchanged. The conclusion is the entire
`IsBorelSubgroup i_K`, with all five fields:

- `IsClosedSubgroup i_K`, meaning that the underlying scheme morphism is
  a closed immersion;
- smoothness of `B_K` over `Spec K`;
- connectedness of the underlying space of `B_K`;
- `IsSolvableGroupScheme B_K`;
- maximality: for every group scheme `B'` over `Spec K`, every
  `i' : B' ⟶ G_K` that is a closed immersion with smooth, connected,
  solvable source, and every `f : B_K ⟶ B'` satisfying `f ≫ i' = i_K`,
  the homomorphism `f` is an isomorphism.

Thus maximality tests every such subgroup over the target field, including
ones not presented as base changes of subgroups over `k`. Neither a
rational-point range condition nor the first four fields alone is the
conclusion.

## Original source and correspondence

J. S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, provides the source assertion:

- Definition 17.6, printed p.353 (one-based PDF p.369), defines a Borel
  subgroup of a connected group variety over an algebraically closed
  field as a maximal connected solvable subgroup variety.
- §17.66, printed p.375 (PDF p.391), uses completeness of `G/B` to
  define Borel subgroups over an arbitrary field, identifies that
  definition with Definition 17.6 over an algebraically closed field,
  and states preservation and reflection under arbitrary field extension.

The present proposition takes the preservation direction of §17.66 with
both fields algebraically closed. The ambient scheme is affine and smooth;
smoothness gives local finite presentation and affineness gives
quasi-compactness, hence the group is of finite type over the field.
Together with connectedness, these are the connected affine group-variety
hypotheses. A smooth closed subgroup of this ambient group is also affine
of finite type. The Library's factorization formulation of maximality
expresses maximality among these actual subgroup varieties. This matches
Definition 17.6 after the solvability comparison below.

The Library's maximality predicate over a general field only tests
subgroups defined over that field. The correspondence here concerns
algebraically closed `k` and `K`; it makes no identification of that
general-field predicate with Milne's geometric Borel notion.

## Solvability and the further chosen algebraic closure

The same registered original supplies the comparison route:

- Propositions 6.20(b) and 6.21, printed p.130 (PDF p.146), identify the
  geometric points of derived groups with the derived abstract groups
  of points in the smooth affine setting.
- Definition 6.26, printed p.131 (PDF p.147), defines algebraic
  solvability using a subnormal series with commutative quotients.
- Proposition 6.30 and Corollary 6.31, printed p.132 (PDF p.148),
  characterize algebraic solvability by termination of the derived
  series and show its invariance under field extension for an affine
  or smooth algebraic group.

For a field `F`, the existing `IsSolvableGroupScheme H` tests Mathlib's
`Group.IsSolvable` on the abstract group

```lean
Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure F)))) ⟶
  ((GroupScheme.baseChange (toAlgebraicClosure F)).obj H).X
```

These are the `AlgebraicClosure F`-points of the base change of `H`.
In particular the input uses `AlgebraicClosure k`, and the conclusion
uses `AlgebraicClosure K`, even though `k` and `K` are algebraically
closed. Neither chosen closure is definitionally the original field.
An algebraic closure of an algebraically closed field is isomorphic to
that field over the field. A future proof must account for the resulting
scheme and point-group isomorphisms, or an equivalent compatible-closure
argument, and formalize the comparison with algebraic solvability via
the cited derived-series results. These comparisons are future proof
obligations, not hypotheses or results of this module.

The official errata, registered source
`milne-2017-algebraic-groups-errata-2026-11-02`, retained HTML snapshot
dated 2026-11-02, was read in full. It lists no correction to the cited
passages.

This is a derived translation of Milne's assertion to the Library's
actual categorical objects and chosen-closure solvability predicate.
The Lean declaration has no extra closure-comparison, reductivity,
torus, parabolic-extension or Borel-extension premise. Its only import
is the existing Borel definitions module; it does not use the dynamic
description of parabolics.
