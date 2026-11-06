# Full-domain intersections between two members of a special cover

Worker 1685 constructs the literal full local-domain intersection of any full
domains `U` and `V` in two original members of a finite chart family with
represented original overlaps. When that pair's original genuine tensor overlap
map is admissible, the genuine tensor map of the two unchanged domain algebras
to this intersection is admissible as a proved conclusion.

The coefficient, ambient-space and original-index universes are independent.
Arbitrary positive radii, trivial coefficient valuations, nonreduced and zero
algebras and empty domains are retained. No global ambient Hausdorff assumption
or supplied intersection of `U` and `V` is used.

This is internal derived infrastructure for the local step of Berkovich,
*Étale cohomology for Non-Archimedean Analytic Spaces* (1993), Lemma 1.2.12,
printed p.20 / PDF p.17, registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The implementation derives the result from the actual `SpecialChartCover`,
Worker 1582's `DomainProduct`, the full-domain pullback construction and the
proved admissible pushout construction. Supporting helper pairs are reused
unchanged and credited.

`domainIntersection` pulls the full product domain `U.product V` back to the
original overlap algebra along the actual finite-presentation overlap map.
Thus it is a full domain in the original overlap chart. Its literal ambient locus
is `chart_i '' U.locus ∩ chart_j '' V.locus`. The locus proof uses the two entire
overlap leg equations and the original chart embeddings; the reverse direction
uses the given literal original overlap to recover its unique chart point.

`domainIntersectionLeftMap` and `domainIntersectionRightMap` compose the actual
product algebra legs with the right leg of this pullback pushout. Their
structural equations are proved. Full-domain uniqueness identifies them with the
canonical local-domain inclusion restrictions constructed from ambient
containment. Consequently the algebra maps in the conclusion are precisely
those of the actual full-domain category.

The original finite-presentation overlap map is admissible because its composite
with the constructed tensor comparison is the given admissible genuine tensor
overlap map. Admissible pushout proves that the new right leg is admissible.
The product algebra is boundedly equivalent to the coproduct of the unchanged
two domain algebras, and that coproduct is boundedly equivalent to their genuine
completed tensor. The bounded-section criterion and composition give the
required two-sided quotient-seminorm comparison and surjectivity.

The inputs here must be full domains in two original members of the given
finite special-cover family. Arbitrary local domains inside its union may span
several members. Descent across the finite product cover is still needed to
prove the full `SpecialSetIntersectionStatement`; it is not assumed or proved
by this unit.
