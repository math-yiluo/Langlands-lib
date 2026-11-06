# Unchanged-algebra local intersections subordinate to a special cover

Worker 1685 extends the proved special-cover member intersection construction
to arbitrary full local domains whose literal loci lie in two chosen original
members of the finite cover. Each input keeps its original actual algebra,
regardless of its original presentation chart. Coefficient, ambient-space and
original-index universes remain independent.

This is internal derived infrastructure from the actual original-chart
reexpression and coherence results, the full `LocalDomain` category and
`SpecialCoverDomainIntersection`. Supporting helpers, including Worker 1582's
unchanged domain product and closed-ideal extension constructions, are credited.
No new original-source assertion is used.

`LocalDomain.reexpress` uses the proved full-domain reexpression in a containing
original chart. Its algebra is exactly the input algebra and its literal ambient
locus is unchanged. `reexpressIso` stores bounded identity maps in both
directions; its full original-chart structural equations are the existing
reexpression coherence equations.

For full local domains `U,V` contained in chosen original members `i,j`,
`localIntersection` applies `domainIntersection` to their reexpressions.
`localIntersection_locus` is the exact literal intersection of the two input
loci. The two inclusions are the canonical full-domain restrictions from
ambient containment. Thinness identifies them with the previously constructed
inclusions composed with the inverse reexpression isomorphisms. Since these
isomorphisms have bounded identity restrictions, the two entire original algebra
maps are unchanged.

`localIntersection_tensor_isAdmissibleEpi` therefore applies the existing
tensor-admissible intersection result using precisely `U.algebra`, `V.algebra`
and the canonical local-domain inclusion restrictions. Its only additional
premise is admissibility of the corresponding original overlap tensor map, as
supplied by a special cover.

The construction retains arbitrary positive radii, trivial valuations,
nonreduced and zero algebras, and empty domains, without global ambient
Hausdorffness. It supplies the individual local intersections for a finite
subordinate cover. The descent needed to assemble them across the entire
special subset remains a separate obligation.
