# Integral conjugation covariance and direct residue parabolic attainment

This internal supporting unit proves
`UnramifiedResidueParabolicAttainmentStatement` at arbitrary universe `u`.
It retains all seven building hypotheses, all eight apartment-descent
hypotheses, and the actual all-facet unramified integral-point
characterization from `UnramifiedFacetParabolicOrderStatement`. For an
apartment point `x`, a supplied reductive quotient of the actual family model
at the facet containing `x`, and any parabolic subgroup over the original
residue field, an incident facet has exactly that subgroup functor as its
actual schematic quotient image. The theorem is
`unramifiedResidueParabolicAttainment`.

The target facet is still required to contain a point of the distinguished
apartment. This unit does not prove image parabolicity for every incident
facet, injectivity, or the full facet order bijection.

The provenance is an internal composition of existing Library extension,
generic rigidity, building action, schematic-image functoriality and residue
parabolic-attainment results. There is no additional translation claim about
the original literature.

## Compatible conjugation of actual neutral models

For any actual integral model over a domain with fraction field, `innerHom`
is the model's inner automorphism at an actual integral section, compatible
with the generic inner automorphism at its integral-point image. Its generic
compatibility is the base-change and homomorphism naturality of inner
conjugation. `innerHom_specialFibreMap` says its actual residue morphism is
inner conjugation at the reduction of that same section.

For a facet-model family satisfying the all-facet unramified integral-point
characterization, `exists_neutralConjugationHom` extends generic conjugation
from the neutral model of a facet to that of its translate. Indeed,
conjugation preserves the normal zero subgroup and carries the pointwise
fixer of the image facet to that of the translated image facet, by the
equivariance of the given building map. The published unramified smooth
extension theorem applies to these actual integral-point subgroups.
`exists_neutralConjugationIso` applies the extension in the reverse direction
and uses generic rigidity to produce inverse actual model morphisms.

If the building map is injective, an actual integral section of the target
neutral model fixes its target facet pointwise: its unramified image fixes
the image facet by the characterization, and equivariance plus injectivity
reflect this equality downstairs. Thus `facetTranslateEquiv_integralPointMap`
identifies the translated target facet with the original target facet.

## Covariance of actual schematic quotient images

`neutralConjugationIso_comp_morphism` compares the translated source model
isomorphism followed by the supplied incident-facet morphism with the original
supplied morphism followed by target inner conjugation. Both composites
extend the same generic inner automorphism, so `IntegralModel.Hom.hom_eq`
identifies them. No compatibility between arbitrary choices of extensions or
family morphisms is assumed.

`exists_translated_incidentFacet_quotientImage` translates an incident source
facet by the integral-point image of the section. Incidence is preserved
because the target facet is fixed. The preceding equality of actual model
morphisms remains an equality after residue base change. Naturality of
inner conjugation then moves target conjugation through the supplied
quotient projection. Precomposition by the actual residue isomorphism of
source models leaves the schematic-image subgroup functor unchanged.
Consequently the translated facet's actual quotient image equals the
schematic image of the original comparison followed by inner conjugation at
the projected reduction. This identity holds on every test scheme and does
not require the quotient to be reductive.

## Direct parabolic attainment

The published supporting theorem
`unramifiedResidueConjugateAttainment` constructs an integral section and an
incident facet whose inverse-conjugated schematic quotient image is the
specified residue parabolic. Apply the covariance lemma to the inverse of
that section. Reduction and quotient projection are group homomorphisms,
so their composite sends the inverse section to the inverse projected
residue point. The inner automorphism at an inverse point is the inverse
inner automorphism. The new translated incident facet therefore has the
specified parabolic as its actual, unconjugated quotient image. All generic
torus and integral-torus constructions remain supplied by the imported
attainment theorem; they are not extra hypotheses of the final statement.
