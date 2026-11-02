# Ambient geometry for coherent families over a field

This is an internal helper for the actual coherent-family atlas construction.
`HasAtlasAmbientGeometry f` means that the actual scheme morphism `f` is
separated and flat, locally of finite presentation, and quasi-compact.
Together these give the separated, flat, finite-presentation ambient hypotheses:
separatedness also implies quasi-separatedness. The definition records only
these geometric properties and makes no representability or atlas assertion.

`HasAtlasAmbientGeometry.relativeProjection` proves the same properties for
`(Picard.relativeProjection f).app T` for every actual test scheme `T` over
the base. It uses the existing definition as the first projection from the
chosen fibre product and the base-change instances for the four properties.
There are no restrictions on the test scheme.

`flat_over_field` proves flatness of every scheme morphism to `Spec k`.
The Mathlib instance uses the integral one-point target and affine charts,
where a ring homomorphism out of a field is flat. No properness or smoothness
hypothesis enters this step. `locallyOfFinitePresentation_over_field` uses
that the spectrum of a field is locally noetherian and Mathlib's implication
from local finite type over a locally noetherian scheme to local finite
presentation.

`properField_hasAtlasAmbientGeometry` combines these two results with the
separatedness, local finite type, and quasi-compactness supplied by properness.
Its only geometric hypothesis is `IsProper X.hom`. The final lemma applies
the base-change result to every scheme over the field. All declarations retain
the arbitrary universe `u`, include imperfect fields, and impose no
projectivity, reducedness, connectedness, rational point, or section.

The provenance is internal: this module packages existing Mathlib geometric
properties and proves their implications for the published actual relative
space. It does not supply the algebraicity, affine diagonal, local finite
presentation of the coherent stack itself, or a smooth surjective atlas.
