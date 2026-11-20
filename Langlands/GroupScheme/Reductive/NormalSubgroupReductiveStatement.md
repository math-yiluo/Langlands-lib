# Smooth connected normal subgroups of reductive groups are reductive

`Langlands.GroupScheme.NormalSubgroupReductiveStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `k : Type u` be a field, put `S = Spec (CommRingCat.of k)`, and let
`G : GroupScheme S` satisfy `IsConnectedReductive G`. Let `N : GroupScheme S`
and `n : N ⟶ G` satisfy `IsClosedSubgroup n`, `Smooth N.X.hom`,
`ConnectedSpace N.X.left` and `(SubgroupFunctor.range n).IsNormal`. Then
`IsConnectedReductive N`.

The ingredients are existing declarations, used without change.

- `IsConnectedReductive G` (from [`Reductive.Basic`](Basic.md)) says that
  `G` is smooth, affine and connected over `k`, and that its base change to
  `k̄ = AlgebraicClosure k` has trivial unipotent radical: every smooth
  connected unipotent normal closed subgroup of `G_{k̄}` is trivial.
- `IsClosedSubgroup n` (same module) says that the underlying morphism of
  schemes of `n` is a closed immersion.
- `SubgroupFunctor.range n` (from [`SubgroupFunctor`](../SubgroupFunctor.md))
  is the subgroup functor of `G` of points in the image of `n`; `IsNormal`
  says that it is stable under conjugation by points of `G` over every test
  scheme.
- `Smooth` is from Mathlib; `ConnectedSpace N.X.left` says that the
  underlying topological space of `N` is connected.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Corollary 21.53, p.441: "Every connected normal subgroup variety N of a
  reductive group G is reductive."
- Chapter 21 opening, p.424: "The field k is arbitrary."
- 6.46, p.135: "Let G be a connected group variety over k. It follows from
  6.45 that among the connected normal unipotent subgroup varieties of G,
  there is a largest one. This is called the unipotent radical R_u(G) of G.
  A connected group variety G over an algebraically closed field is said to
  be reductive if R_u(G) = e. A connected group variety over a field k is
  said to be reductive if G_{k^a} is reductive, i.e., if its geometric
  unipotent radical R_u(G_{k^a}) is trivial."
- Chapter 9 opening, p.163: "Recall that all algebraic groups are affine
  over a base field k."
- p.13: "“group variety” = “smooth algebraic group”." Proposition 1.41,
  p.18: "Algebraic subgroups of algebraic groups are closed (in the Zariski
  topology)."

Milne's proof, for orientation only: "We may suppose that k is
algebraically closed. The quotient N/N ∩ R(G) is a normal subgroup variety
of the semisimple group G/R(G), and so it is semisimple. Therefore
R_u(G) ⊂ N ∩ R(G), which is of multiplicative type, and so R_u(G) = e." The
two occurrences of `R_u(G)` in the last sentence should read `R_u(N)`:
`R_u(G) = e` is the hypothesis, and the conclusion to be shown is
`R_u(N) = e`. With this reading the argument is: `R_u(N)` maps to a
connected unipotent normal subgroup of the semisimple group `N/N ∩ R(G)`,
so it maps to `e` (a semisimple group is reductive) and lies in
`N ∩ R(G)`; as `R(G)` is a torus for reductive `G` (Proposition 21.60,
(a)⇒(b), p.442), its unipotent subgroups are trivial.

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Corollary 21.53 on
printed p.441 as "Every smooth connected normal subgroup N of a reductive
group G is reductive", which has the same meaning ("subgroup variety" means
smooth algebraic subgroup). Its proof has the same slip. Its 6.46 on p.135
has the same words as quoted, and its Chapter 9 opening on p.163 contains
the quoted affineness sentence with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. Neither has an entry for p.135, 163, 424 or 441. The
2017 errata entry for p.440 concerns the proof of Theorem 21.51, and the
2022 errata entry for p.440 corrects a cross-reference; neither concerns
Corollary 21.53. The 2017 entry for p.18 concerns the proof of Lemma 1.40,
and the 2022 errata entry for p.13 corrects an inequality for tangent
spaces, not the definition of group varieties (on p.14 of the reprint).

## Derivation from the source

- **The reductive group.** By 6.46, a reductive group over `k` is a
  connected group variety (smooth, p.13) whose geometric unipotent radical
  is trivial, and it is affine by the standing convention (p.163). This is
  `IsConnectedReductive G`. The field is arbitrary (Chapter 21 opening).
- **The subgroup.** "A connected normal subgroup variety N" is a smooth,
  connected, normal algebraic subgroup. Algebraic subgroups are closed
  (Proposition 1.41), so this is `IsClosedSubgroup n`, `Smooth N.X.hom`,
  `ConnectedSpace N.X.left` and `(SubgroupFunctor.range n).IsNormal`.
  Milne tests normality on points with values in `k`-algebras; `IsNormal`
  tests all schemes over `Spec k`, which gives the same condition for a
  closed subgroup, since membership of a point in a closed subscheme can be
  checked on an affine open cover of the test scheme.
- **The conclusion.** "`N` is reductive" is `IsConnectedReductive N`. The
  affineness of `N`, which `IsConnectedReductive N` includes, follows from
  that of `G` because `n` is a closed immersion.
- **Universes.** One universe `u` is used for the field and the schemes.
  This is a formalization convention.
