# Finite iterated unit-radius Laurent covers

Author: Worker 84.

For a complete ultrametric normed field `K : Type u` and a presented strict
affinoid algebra `P`, `RationalData.iteratedLaurent g ε` is an actual rational
datum for a tuple `g : Fin m → P` and a Boolean choice `ε : Fin m → Bool`.
The convention is `false` for the upper inequality `x(g) ≤ 1` and `true`
for the lower inequality `1 ≤ x(g)`. The constructor recursively intersects
the first selected binary datum with the tail leaf and starts with `whole`
when `m = 0`. All Boolean leaves remain in the family, including leaves
whose loci are empty. The associated algebra is the existing closed-ideal
Tate quotient of this datum.

`mem_locus_iteratedLaurent` proves that membership is exactly the conjunction
of the selected real inequalities. `iteratedLaurent_covers` assigns each
spectrum point a choice by deciding each upper inequality; its negation
implies the lower inequality. The same proof covers the empty tuple and the
zero base. `iteratedLaurent_familyCovers` expresses this as the existing
`FamilyCovers` predicate, with `ULift.{u} (Fin m → Bool)` to place the finite
index in the universe required by that predicate. It remains a finite index.
`iteratedLaurentFactor`, `iteratedLaurentHead` and `iteratedLaurentTail` are
actual rational inclusions.

For any bounded algebra map `φ : P → Q`,
`locus_iteratedLaurent_pullback` identifies the locus of the pulled-back leaf
with the leaf of the mapped tuple. `iteratedLaurentPullbackIso` packages both
inclusions as an isomorphism in the rational inclusion category. Restrictions
along its inverse turn the existing quotient comparison into the actual
bounded homomorphism `iteratedLaurentComparison`. Its `_comp_baseMap` lemma
identifies its composite with the source base map. The
`iteratedLaurentComparison_restriction` lemma is the commuting square for
any inclusion from a leaf to another rational datum, using the explicitly
transported `iteratedLaurentPullbackInclusion`.

`iteratedLaurentBranchEquiv` combines the existing relative comparison for
the inclusion of a nonempty leaf in its first branch with an equal-locus
isomorphism on that branch quotient. The first inequality holds at every
spectrum point of the branch quotient, so the pulled-back full leaf has the
locus of the tail leaf of the images of the remaining functions. The result
is a bounded equivalence of the actual quotient algebras. Its base-map square
is `iteratedLaurentBranchEquiv_comp_baseMap`; the `_restriction_head` and
`_restriction_tail` lemmas identify restriction from the first branch with
the new tail base map and restriction from the old tail with its bounded
base-change comparison.

`iteratedLaurentOverlapPullbackIso` and
`iteratedLaurentOverlapComparison` give the corresponding constructions for
the chosen pairwise intersections of leaves. Their base-map and left/right
restriction squares follow from the rational universal property `hom_ext`.
`iteratedLaurent_compatible_comparison` applies those squares to show that
pairwise compatible actual quotient sections remain compatible after any
bounded base change.

For repeated binary gluing on a quotient base, `laurentChild d g b` is the
transparent alias for `d.inter (laurentChoice g b)`, where `d` is any rational
prefix, and `laurentChild_covers` covers its locus by its two children.
`laurentChildPullbackIso` and `laurentChildEquiv` identify a global child over
the prefix quotient with the ordinary binary Laurent datum of `d.baseMap g`.
Their base-map and prefix-restriction squares are proved. The transparent
alias `laurentChildrenOverlap` is the chosen intersection of those two global
children. Its pullback isomorphism and bounded quotient equivalence identify
it with the intersection of the two local binary Laurent data. The
`laurentChildrenOverlapEquiv_comp_baseMap`, `_left` and `_right` lemmas prove
the base-map and two restriction squares. All these comparisons use the
existing relative quotient equivalence and rational restrictions; the equal
locus isomorphisms do not require equality of the chosen presentations.

These are elementary constructions and comparison proofs in every universe
`u`. They allow trivial scalar valuations and zero or nonreduced presented
bases. The all-unit restriction belongs to the separate standard-cover
refinement construction: this module takes arbitrary elements `g`. It gives
an interface for a later induction using binary descent and asserts no
scalar descent or sheaf theorem.

Provenance: Achinger, *Introduction to non-Archimedean Geometry* (November 22,
2020), Corollary 7.1.2, p.65, describes the finite Laurent cover. The all-unit
refinement motivating its use is on p.67. Source ID
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
Berkovich, *Non-archimedean analytic spaces*, Trieste 2009, Exercise
2.2.2(i)–(iii), pp.9–10, gives the Laurent inequalities, quotient equations
and intersection context; source ID `berkovich-2009-trieste-analytic-spaces`,
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The recursive chosen presentations and explicit quotient comparisons here
are derived from that geometric construction and the published rational
universal properties. Achinger assumes nontrivial valuation on p.6; none of
these elementary constructions chooses a small scalar or uses that
assumption.
