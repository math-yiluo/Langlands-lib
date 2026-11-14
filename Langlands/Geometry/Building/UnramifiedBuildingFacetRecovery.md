# Recovering full unramified building facets from zero fixers

This internal derived construction works at arbitrary universe `u` on the
actual maximal-unramified integer-valuation quotient and its existing full
building facets. It extends the apartment recovery result to the entire
building. It introduces no extra apartment, Tits-system or common-apartment
premise for the unramified result.

The generic helper first uses a supplied common-apartment property to move
any quotient point fixed by a singleton sharp fixer into the original
apartment. The existing root-jump fixed-locus theorem then puts that point
in the affine-root closure of the singleton's facet.

For the actual unramified zero subgroup, let two nonempty subsets lie in
two full building facets. If the zero fixer of the first subset is contained
in the zero fixer of the second, the second facet precedes the first.
The proof chooses a chart of the first facet and one point of each subset.
Facet constancy and pointwise fixation put the conjugate singleton sharp
fixer in the first subset's zero fixer. Normality of the supplied zero
subgroup supplies the zero-subgroup membership after conjugation. The
assumed inclusion makes this sharp fixer fix the point of the second
subset. The published maximal-unramified common-apartment theorem and the
generic helper put this point in the first facet's combinatorial closure.
The existing full-facet partition and closure incidence criterion give the
claimed incidence.

Mutual incidence gives facet equality. Thus `buildingFacetZeroFixerEmbedding`
is the specified embedding of every full building facet into its actual
zero-fixer subgroup; its application formula is definitional. The subsets
need not be full facets or share an initially supplied chart.

The provenance is internal composition of the imported root fixed-locus,
common-apartment, zero-subgroup normality, facet-constancy, partition and
closure theorems. This module does not assert parabolicity, classification
of parabolics, congruence containment or descent of facets to the base field.
