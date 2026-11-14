# Composition and opposite inclusion for integer-facet residue images

This internal derived module uses the original `IntegerValuationBuildingData`
and a supplied `IntegerFacetModelData` over a domain with its specified fraction
field. A local ring is needed for the special-fibre conclusions. The models,
their incidence morphisms, and the special-fibre quotient remain supplied.
No Henselian, residue-separability, characteristic, or root-system premise is
needed for these functoriality deductions.

`neutralMap_comp` proves that the actual neutral model map for `F ≺ D` is
the composite of those for `C ≺ D` and `F ≺ C`. Both sides extend the
identity of the same original generic group. The published
`IntegralModel.hom_eq_of_generic` makes them equal, using the specified
generic compatibility squares. `neutralSpecialFibreMap_comp` applies the
residue-field base-change functor to this equality. Thus these actual maps
are coherent without a separate coherence hypothesis.

`incidentParabolicImage_le` proves that `F₁ ≺ F₂` gives containment of the
image for `F₂` in the image for `F₁`, in the specified quotient at `F`.
The proof rewrites the map for `F₂` by the actual special-fibre composition
law and applies `SchematicImage.range_inclusion_comp_le`. These images
are the all-test ranges of actual schematic-image inclusions; the argument
does not replace them with the pointwise ranges of the original maps.

`hasFacetParabolicOrderBijection_iff_bijOn` therefore removes the reversed
inclusion clause from the outstanding correspondence obligation. Its
bijection clause still asserts parabolicity, injectivity, and surjectivity
and is not proved here. `ImageFunctorialityStatement` packages the
special-fibre composition law, reversed containment, and this equivalence;
`imageFunctoriality` proves their conjunction.

The provenance is an internal deduction from generic rigidity and
schematic-image functoriality. This module establishes neither model
existence nor coefficient comparison isomorphisms, the facet-parabolic
bijection, or the prescribed-point split-torus theorem.
