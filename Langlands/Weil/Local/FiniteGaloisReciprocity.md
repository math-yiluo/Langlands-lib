# Reciprocity on a finite Galois Weil kernel

For a specified finite Galois embedding of p-adic fields, the actual finite
Galois quotient of the local Weil group identifies its kernel continuously
with the local Weil group of the extension. A supplied geometric reciprocity
candidate therefore gives a continuous, surjective homomorphism from this
kernel to the extension field's multiplicative group by taking the inverse of
the candidate's value. Its restriction along the extension Weil map is
exactly inverse geometric reciprocity.

Conjugation by an element of the base Weil group preserves the quotient
kernel and transports to a continuous automorphism of the extension Weil
group. The transported automorphism preserves the integer degree: the
extension Weil map multiplies that degree by the positive residue degree,
and conjugation preserves degree in the base Weil group. Under the supplied
order normalization, the kernel reciprocity homomorphism has negative
degree, and its order is invariant under this conjugation.

These are derived constructions from `FiniteGaloisQuotient`, the published
rank-one reciprocity map, and elementary conjugation identities. This module
does not prove equivariance of the full field-valued map or identify the
Weil extension's second cohomology class with the arithmetic fundamental
class. Those obligations remain in the local Weil class-map proof.
