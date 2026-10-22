# Negative-degree corestriction and norm-kernel representatives

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

This module proves the degree-minus-one representative formula for
the constructed subgroup corestriction. A vector with zero subgroup norm also
has zero full norm, by the proved factorization of the full norm through the
coset norm. Corestriction carries its actual Tate class to the class of the
same vector for the full group.

The proof lifts the vector through the actual coinduced augmentation sequence.
Its subgroup norm lifts to an invariant in the kernel. The coset norm of that
invariant maps to the full norm of the original lift. The explicit splice
connecting-map formula, degree-zero corestriction formula, and injectivity of
the actual dimension-shifting isomorphism identify the degree-minus-one map.
No representative formula or connecting compatibility is assumed.

Source: Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VII, section 7,
printed pages 118–119 (PDF pages 124–125), and Chapter VIII, section 1, printed
pages 127–129 (PDF pages 133–135). This is generic finite-group theory in the
full supported carrier universe.
