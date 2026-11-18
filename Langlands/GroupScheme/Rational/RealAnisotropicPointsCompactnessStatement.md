# Compact real points of an anisotropic semisimple group

Worker 862.

`Langlands.GroupScheme.RealAnisotropicPointsCompactnessStatement : Prop`
states that every anisotropic semisimple group scheme over the actual real
numbers has compact real points. It has no universe parameters. This module
introduces the proposition and does not prove it.

The quantified group is `G : GroupScheme (Spec (CommRingCat.of ℝ))`.
`IsSemisimple G` gives a connected reductive group with finite
scheme-theoretic centre. In particular it supplies affineness and smoothness.
`IsAnisotropic G` means that the split rank is zero, equivalently that every
closed split subtorus has dimension zero. These predicates are unchanged
Library definitions.

The point group `rationalPoints G` is the group of morphisms
`Over.mk (𝟙 (Spec ℝ)) ⟶ G.X`. Its topology is explicitly
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology ℝ G.X`,
using the usual topology on `ℝ`. This is the canonical affine evaluation
topology: regular functions on the affine scheme give the coordinate
evaluations. The affine instances used to construct it come from
`hG.isConnectedReductive.isAffineHom`. The conclusion is compactness of
the entire point set, expressed as `IsCompact Set.univ`. There is no
supplied representation, compactness premise, or additional topological
choice.

## Source correspondence

Kazuo Suzuki, *A note on a theorem of E. Cartan*, Tohoku Mathematical
Journal 23 (1971), 17–20, source ID `suzuki-1971-cartan`, readable PDF
SHA-256 `208820540ee03a5bd60b7d8cf5065c691a21d60013fa497a008882108da99602`.
The relevant location is Remark 2 on printed p. 17 (PDF page 1).
The publisher gives DOI `10.2748/tmj/1178242683`; the initially registered
citation metadata contains a DOI typo, but the registered PDF and URL
identify this article.

Remark 2 identifies compactness of the rational-point group over a local
field, explicitly including `ℝ`, with anisotropy of the algebraic group.
We use only its forward implication from anisotropy to compactness and
restrict to the semisimple groups required by Milne's Theorem 25.57.
For this scope, split-rank-zero anisotropy agrees with Milne's convention;
see the source comparison in
[`RealAnisotropicMaximalTorusConjugacyStatement`](RealAnisotropicMaximalTorusConjugacyStatement.md).
The actual real-point topology is expressed by the canonical evaluation
topology rather than an unspecified topology on an abstract group.
This is a derived specialization of the cited assertion.

Suzuki's description of anisotropy in terms of Borel subgroups is not
used as a Lean definition. The statement uses only the Library's split
rank predicate. The introductory version of his Theorem 2 on p. 17
omits compactness; that version is also not used here.

## Role in the conjugacy proof

Together with
[`RealCompactMaximalTorusConjugacyStatement`](RealCompactMaximalTorusConjugacyStatement.md),
this proposition implies the unchanged
`RealAnisotropicMaximalTorusConjugacyStatement`. Both compactness
statements use the same real point group and the same affine instances.
The existing nonarchimedean compactness theorem cannot supply this
real-field input.
