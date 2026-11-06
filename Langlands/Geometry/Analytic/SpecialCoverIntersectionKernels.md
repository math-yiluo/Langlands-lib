# Compatible actual kernels on a subordinate product cover

Worker 1582 specializes the generic product-intersection kernel construction to
two finite full-domain covers subordinate to a special finite chart cover.
Worker 1685's unchanged-algebra local intersections supply the local quotient
targets. This is internal derived infrastructure; it makes no additional
original-source assertion.

The relative algebra cover of each full local domain has exactly the original
covering algebras. Extending its members through the containing local domain
recovers the original literal local loci, by the proved relative-extension locus
identity. Consequently the same containing original chart can be used in the
special-cover intersection construction.

`SubordinateProductIntersection.cover` is the actual finite full-domain product
cover of the unchanged affinoid coproduct. Its ordinal indices are identified
with pairs of the original subordinate indices. `intersection` constructs the
full local intersection for each pair of extended relative domains, retaining
the two canonical bounded inclusion restrictions. `quotientMap` is the actual
bounded quotient of the corresponding product-domain algebra. Specialness of
the original chart cover proves its admissibility via the genuine local
completed-tensor map.

`ideal` is the exact ring kernel of that quotient, including nilpotent
information. It is closed by continuity. `idealCompatible` applies the generic
closed-kernel equality to the actual intersection of any two product-cover
members and its original pushout restriction maps. Thus the kernels satisfy
precisely the published finite closed-ideal compatibility condition.

`globalIdeal` is the explicit intersection of their contractions to the original
coproduct algebra, and is closed. No effectiveness assertion is proved or assumed
here: identifying its closed local extensions with the supplied local kernels
remains the separate ideal-effectiveness proof obligation. Coefficient,
ambient-space and original-index universes remain independent; empty covers and
zero or nonreduced algebras are retained.
