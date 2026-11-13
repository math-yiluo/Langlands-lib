# Local-model and bounded-normalizer inputs on actual facets

This internal adapter works over a nonarchimedean local field at arbitrary
universe `u`, with a supplied `KPBuildingDatum D` and its single-group
axioms. It applies two explicit proposition inputs to the actual facet
models and positive subgroups used by `AvailableMaximalProPStatement`.
It does not prove either input.

`isProP_facetPositiveSubgroup` takes a proof of
`LocalFieldPositiveProPStatement` in the same universe. Connected
reductivity of the generic group supplies smoothness and hence local
finite type. The facet reductive-quotient axiom supplies
`IsReductiveQuotient` for the actual quotient of the actual facet model.
Applying the supplied local-model theorem proves that the existing
`facetPositiveSubgroup D Fa` is pro-p for the residue characteristic.
No separate model or filtration is chosen.

`isAlgebraicallyBounded_facetPositiveNormalizer` takes a proof of
`BoundedOpenNormalizerStatement` in the same universe. The actual facet
positive subgroup is open and compact in the canonical point topology.
As an open subgroup of a topological group it is closed, so the proved
local-field affine boundedness/compactness comparison makes it
algebraically bounded. The supplied bounded-normalizer theorem then
applies to this subgroup. Its conclusion is algebraic boundedness of the
normalizer intersected with the actual rational common norm kernel;
the norm kernel is the one occurring in that theorem.

`isChamber_and_normalizer_eq_of_maximal_from_inputs` applies these two
adapters to `isChamber_and_normalizer_eq_of_maximal`. It also retains the
explicit facet reductive comparisons and finite normal-Sylow torus
input. If a facet positive subgroup is maximal in the existing global
sense, the facet is a chamber and its normalizer intersected with the
zero subgroup equals its zero fixer.

`maximalFacetPositiveChamber` packages this result as a subtype: its value
is the given facet, together with chamberhood and the normalizer identity.
The constructor retains all the explicit inputs of the preceding theorem.
`maximalFacetPositiveChamber_val` is the definitional equality showing
that the constructor refines the original facet.

The provenance is internal specialization of the named Library
interfaces. The smooth-model pro-p theorem, bounded-open-normalizer
theorem, finite normal-Sylow theorem and facet comparisons remain
explicit hypotheses. This module does not prove the full corrected
KP Proposition 13.5.2 or treat any unproved Library proposition as an
available theorem.
