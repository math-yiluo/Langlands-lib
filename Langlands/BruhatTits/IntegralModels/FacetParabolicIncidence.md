# Incidence and actual special-fibre images

This internal supporting construction concerns any supplied `FacetModelData B R`
over an integral domain with fraction field `K`, where `K` is a nonarchimedean
local field and `R` is local. It defines
`FacetModelData.incidentSpecialFibreImage` as the all-test range of the actual
schematic-image inclusion of the neutral special-fibre map. No parabolicity,
model-characterization, reductive-quotient validity, or building axiom is assumed.

For incident facets `F₁` and `F₂` above `F`, if `F₁` precedes `F₂`, both their
neutral special-fibre images and their actual images in any supplied
`SpecialFibreQuotientData (M.model F)` satisfy the opposite inclusion:
the image indexed by `F₂` is contained in the image indexed by `F₁`.
The quotient image here is exactly the existing `incidentParabolicImage`,
including when its name does not yet carry a proved parabolicity assertion.
This proves the order clause needed by `HasFacetParabolicOrderBijection`.
It does not establish the bijection or any geometric parabolicity assertion.

The implemented proof first applies the published generic rigidity of flat
affine integral models. A composite of two compatible extensions of the identity
on the generic fibre equals any directly supplied extension of that identity.
Actual residue base change gives the same composition identity on neutral
special fibres. This accounts for arbitrary choices of the incidence morphisms
in `FacetModelData`, without imposing a separate compatibility axiom on them.

The schematic image projection is schematically dominant and its inclusion is
closed. The published closed-containment lemma removes this dominant projection
from a containment assertion. Factoring the second special-fibre map through the
first source therefore proves containment of its entire closed schematic image.
The same argument after composition with the supplied quotient projection proves
`incidentParabolicImage_le`. Every containment is tested on all schemes over the
residue field; no surjectivity on rational points is used.

The provenance is internal: the proofs combine the current Library's
`IntegralModel.Hom.hom_eq`, compatible-model composition, actual residue base
change, schematic-image factorization, and closed containment under a
schematically dominant source factor. No external assertion is added as an
assumption, and the exact unramified facet-order target is unchanged.
