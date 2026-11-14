# Actual incident root images in a reductive quotient at equal depths

This internal supporting module defines the original source-root composite
through a supplied model morphism and the actual radical projection of its
target. The source root map, neutral special-fibre morphism, and quotient
projection are the existing specified maps. The factorization theorem
identifies this composite with the canonical residue root map followed by
the target model's root-to-quotient map.

Over any local integral domain with its supplied fraction field, an invertible
canonical residue root map gives three consequences. The full original
composite has smooth scheme-theoretic kernel. Its differential image equals
the target positive cyclic weight span. The Lie image of the inclusion of its
actual schematic image equals that same span. The torus and character in these
spans are exactly `quotientTorusInclusion` and `characterSpecialization` used in
the facet sign formula.

For kernel smoothness, the residue root isomorphism and identity on the
quotient give an isomorphism of arrows, hence an isomorphism of the actual
scheme-theoretic kernels by the imported `kernelSquareIso`. Smoothness of the
target root-to-quotient kernel transfers through this isomorphism. This uses
the full kernels on every scheme test, including infinitesimal tests.

For the differential range, the residue root isomorphism is smooth, so its
actual differential is surjective. Functoriality of the differential then
identifies the composite range with the target root-to-quotient range.
The imported same-model result computes that range. The integral-torus
comparison lemmas identify its torus and character with the specified facet
ones. The schematic-image assertion applies the imported smooth-full-kernel
Lie-image comparison, using the kernel smoothness just proved.

Finally, for the actual maximal-unramified integers of a nonarchimedean local
field, the module specializes all three results to two supplied characterized
neutral zero-fixer models whose apartment subsets are nonempty and bounded
above under every real affine functional. Equality of the actual root-fixer
depths at a common apartment point makes the canonical residue root map an
isomorphism by `IntegralRootModelMapIso`, discharging the general hypothesis.

These are internal deductions from the imported constructions and proofs.
They require no smoothness of the ambient incident model morphism, no facet
hypothesis, and no inclusion between the subsets. They do not treat strict
depth increase, relate signs to depths, prove smoothness of the full ambient
model kernel, or establish the complete common-torus Lie-weight formula.
