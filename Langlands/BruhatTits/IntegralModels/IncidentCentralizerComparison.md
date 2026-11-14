# Actual centralizer comparisons for zero-fixer models

This internal deduction uses the published integral centralizer construction,
centralizer fixer preimage equality, strictly Henselian smooth extension,
generic rigidity, and smooth restriction to full torus centralizers.

For two smooth maximal-unramified integral models with point images given by
the same zero subgroup intersected with fixers of nonempty apartment subsets,
the constructed integral models of the specified full generic centralizer
have equal original integral-point images. Indeed the images are comaps of
the ambient images, comap preserves intersection, and the centralizer fixer
preimage is independent of the nonempty apartment subset.

The proved smooth extension criterion over maximal-unramified integers extends
the generic identity in both directions. Generic rigidity makes these maps
inverse and gives `modelIso`, a compatible isomorphism of actual integral
models. The same rigidity shows that its composite with the target centralizer
inclusion equals the source inclusion followed by any compatible ambient
comparison. Actual residue base change gives `specialFibreIso_comp`.

For any split integral torus in a relative identity-component model, the full
kernel of its residue centralizer inclusion followed by the radical projection
is smooth. A smooth closed representative of the full torus centralizer in the
quotient exists by the published fixed-subgroup construction. The general
smooth-centralizer restriction theorem applies to the actual radical
projection, which is smooth. This is a full scheme-theoretic kernel conclusion,
including infinitesimal test schemes.

No smoothness of the ambient incident-model map is asserted or assumed. The
common-torus theorem still needs compatible root/centralizer product charts
and the smooth factor-kernel assembly.
