# Cartan subgroups and their closed representatives

Worker 1342.

`Langlands.GroupScheme.IsCartanSubgroup i` is a predicate on an actual group-scheme
homomorphism `i : H ⟶ G` over `Spec k`, for an arbitrary field `k` in universe `u`.
It requires a closed subgroup embedding and a maximal torus `j : T.toGrp ⟶ G`
such that

`SubgroupFunctor.range i = torusCentralizer j`.

The equality is between subgroup functors on **all** schemes over `Spec k`,
including nonaffine and nonreduced tests. The right side requires commutation
with torus points after every refinement of each test scheme. Thus this is an
actual closed subgroup representing a scheme-theoretic centralizer, rather
than a condition only on rational points.

## Source and scope

Milne, *Algebraic Groups* (2017), Definition 17.43, printed p.364
(PDF p.380), defines a Cartan subgroup of a connected group variety as the
centralizer of a maximal torus. Source ID: `milne-2017-algebraic-groups`;
PDF SHA256:
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The Lean predicate extends this defining condition to arbitrary group schemes
over fields. It does not include ambient smoothness, connectedness, affineness
or finite type as defining conditions. On a connected affine group variety it
expresses Milne's definition using the Library's actual maximal-torus and
all-test centralizer interfaces. Applying a structural theorem from Milne still
requires that theorem's ambient hypotheses.

The elementary representative results below are derived interface lemmas:
their proofs use the already published closed representability of centralizers
over fields and uniqueness of represented subgroup functors. They are not
claims to prove Milne's smoothness, connectedness or nilpotence theorem 17.44,
or the generation theorem 17.91.

The final three lemmas are conditional adapters to the existing
`MaximalTorusCentralizerStatement`, the forward direction of Milne's
Corollary 17.84, printed p.379 (PDF p.395). That proposition is an explicit
argument in each lemma. This module does not prove it. The registered complete
errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
contains no correction to 17.43, 17.44, 17.84 or 17.91.

## Implemented results and proof route

- `IsCartanSubgroup.isClosedSubgroup` extracts the closed embedding.
- `isCartanSubgroup_of_representsCentralizer` packages a closed representative
  of a maximal-torus centralizer into the predicate.
- `IsCartanSubgroup.exists_centralizer_representation` recovers a witnessing
  maximal torus and its representation by `i`. Closed immersion gives the
  required monomorphism of schemes over the base.
- `exists_isCartanSubgroup_of_isMaximalTorus` assumes the ambient scheme is
  affine and starts with a given maximal torus. The published
  `hasClosedRepresentative_normalizer_centralizer_range` supplies a closed
  representative of the centralizer of its range. The equality
  `torusCentralizer_eq_centralizer_range` identifies that centralizer with
  `torusCentralizer`. No existence of a maximal torus is established.
- `IsCartanSubgroup.existsUnique_iso_of_range_eq` compares two Cartan embeddings
  with the same all-test image. The existing
  `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` constructs the
  isomorphism compatible with their inclusions. Monicity proves its uniqueness.
  This does not assert equality or an isomorphism over `G` for arbitrary
  different Cartan images.
- `IsMaximalTorus.isCartanSubgroup_of_centralizerStatement` uses the explicit
  centralizer-statement argument and connected reductivity to identify a
  maximal torus with its centralizer.
- `IsCartanSubgroup.exists_iso_maximalTorus_of_centralizerStatement` uses that
  same conditional input to represent the centralizer by the witnessing torus
  itself, then compares its representation with the given Cartan embedding.
- `IsCartanSubgroup.isTorus_of_centralizerStatement` transfers the torus
  predicate across the resulting group-scheme isomorphism with
  `IsTorus.of_iso`.

All results retain arbitrary fields, nonsplit tori, and rank zero. No
perfection, infinitude, rational-point density or generation hypothesis is
used. In the rational-point density project this module supplies only the
Cartan subgroup interface; the general structural and generation arguments
remain separate obligations.
