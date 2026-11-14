# Residue image naturality from actual coefficient comparison squares

This internal derived unit turns actual coefficient comparison isomorphisms
and commutative morphism squares into the Galois compatibility of the actual
facet residue images. The input building, Gamma-facet, models, quotient,
ground residue group and quotient comparison are those of
`GaloisFacetResidueParabolics`. The ground residue group is affine. The
universe and field characteristics are arbitrary.

The general helper `SchematicImage.range_inclusion_galois_of_square`
considers two actual homomorphisms into a group pulled back from the
ground field. If an actual isomorphism from the coefficient pullback of
the first source to the second source intertwines the maps and the
canonical ambient descent isomorphism, their schematic-image subgroup
functors are related by the canonical Galois transport. The proof uses
source-isomorphism invariance, ambient-isomorphism transport and flat
field base-change naturality from `SchematicImageFunctoriality`.

`ResidueCoefficientComparisonData` records actual isomorphisms from the
coefficient pullbacks of the incident neutral special fibres to those of
their Galois translates, and an actual target comparison at the fixed
facet. Its `map_comm` field is the commutative square for the original
neutral special-fibre incidence maps. Its `quotient_comm` field is the
commutative square for the quotient projection followed by the specified
ground-group comparison and the canonical descent isomorphism. None of
these inputs asserts equality of image subgroup functors.

`residueFacetImage_eq_schematicImage` first rewrites the transported
facet image as the actual schematic image of the original neutral map
followed by the quotient and ground-group comparisons.
`hasGaloisResidueImageCompatibility_of_coefficientComparisons` composes
the two supplied morphism squares and applies the general helper.
`GaloisFacetImageNaturalityStatement` expresses this sufficient criterion
using nonemptiness of the comparison data, and `galoisFacetImageNaturality`
proves it.

These are internal consequences of schematic-image functoriality and
the specified morphism squares. Existence of the coefficient comparison
isomorphisms, the two commutative squares, the original models, and the
facet-parabolic bijection remain obligations. This unit does not prove
the maximal-Gamma-facet residue theorem unconditionally or the prescribed
building-point split-torus theorem.
