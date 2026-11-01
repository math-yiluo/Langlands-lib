# Source-refinement Solomon coefficients

Author: Worker 76.

This internal supporting development connects actual source-Levi intersection
refinements to the already proved total type-A Solomon coefficient identity.
It is a finite-coordinate derivation from the imported Library results, with
no use of analytic classification or Aubert identities.

The map from a refinement to the Weyl subgroup of its flattened block shape is
injective. Transpositions test equality of flattened block labels, and the
published nested block-index formulas recover equality of each inner block
partition. The block-Weyl cut correspondence then recovers the positive ordered
block shapes themselves.

The literal flattened Levi equivalence carries the image of the actual refined
Levi under the coarse embedding onto the ordinary flattened Levi subgroup.
The source-Levi image under the same embedding is the ambient Levi
intersection. Testing this equality on permutation matrices gives exactly
`blockWeyl (B.flatten S) = blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w)`.
This uses only the actual source-Levi equality, over any nontrivial commutative
ring; no minimality premise is needed for that individual equality.

`refinementSolomonCoefficient` counts minimal representatives with any given
source refinement, weighted by the ambient signs. Injectivity identifies its
fibers with the source-Weyl intersection fibers in the published
`typeASolomonCoefficientStatement`. The resulting coefficient is the product-Levi
sign, since the flattened length is the sum of the inner lengths. This holds
in every natural rank, including zero, and does not by itself prove commutation
of the actual representation maps.
