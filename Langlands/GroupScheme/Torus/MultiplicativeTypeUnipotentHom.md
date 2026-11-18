# Multiplicative-type subgroups of unipotent groups

`IsMultiplicativeType.unipotentHomEquiv` is the equivalence from the hom-set
of a multiplicative-type group to an affine unipotent group to the one-point
type. Its inverse selects the zero homomorphism; the vanishing theorem proves
that the two maps are inverse.

This internal derived module extends the existing diagonalizable-to-unipotent vanishing
proof to all groups of multiplicative type, including finite nonsmooth groups. It proves
that a closed unipotent subgroup lying in the range of a multiplicative-type subgroup is
trivial on all test schemes, and that restricting a homomorphism to a closed subgroup
preserves multiplicative type of the actual scheme kernel.

The vanishing proof uses `Unipotent.diagonalizable_hom_eq_zero`, the affine coordinate
corepresentation, the defining splitting extension of a multiplicative-type group, and
faithfulness of field-extension pullback. The range statement factors through the given
subgroup, shows the factor is a closed immersion, and applies the vanishing theorem to
the identity of the unipotent group. The full-kernel statement uses the actual pullback
square of `FactoredKernel.map` and closed-immersion stability under base change.

These are derived consequences of the existing Library constructions. No new statement
about the source of an arbitrary extension is assumed in these proofs.
