# Projective generation through irreducible subquotients

This internal criterion concerns actual smooth complex representations of any
topological group, at one arbitrary carrier universe. It uses the published
existence of irreducible subquotients for every nonzero smooth representation,
actual injective/surjective presentations of subquotients and categorical
projective lifting.

For a nonzero map `d : X → Y`, its actual image is nonzero and has an irreducible
subquotient `D`, also a subquotient of `Y`. A nonzero map `P → D` lifts through
a subrepresentation mapping onto `D`, producing a nonzero map from `P` to the
image of `d`. Ambient projectivity lifts this map along the actual surjection
from `X` to that image. Its composite with `d` is nonzero because the image
inclusion is injective. `projectiveSubquotientDetector` chooses this map, and
`projectiveSubquotientDetector_comp_ne_zero` proves that its composite is nonzero.

Consequently, for any full subcategory of smooth representations, if the ambient
object underlying `P` is projective and maps nontrivially to every irreducible
subquotient of each object of the subcategory, `preadditiveCoyonedaInt P` is
faithful. Equality of two Hom maps makes every map out of `P` annihilate the
difference of the original maps, which the first criterion forces to vanish.
This uses no abelian structure or closure property of the full subcategory,
and no finite length or admissibility hypothesis. It is derived from the
imported APIs, rather than a new external structural assertion.
