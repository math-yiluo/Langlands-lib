# Root lengths and symmetric derivative pairings

This internal supporting unit works with the published affine-root-system
predicate, including rank zero and independent universes for the translation
space and its affine torsor.

`HasEqualDerivativeLengths` means that every pair of derivative roots has
equal squared length in the full coroot form. It quantifies over all
derivative roots, including multipliable roots.

The unit proves that the linear part of a root-preserving affine automorphism
permutes all coroot vectors. Consequently, pullback preserves the symmetric
form defined by summing evaluations over that finite set.

Under `HasEqualDerivativeLengths`, the
reflection identity from `AffineSimpleRootGram` and positivity on each root
give symmetry of the full derivative root-coroot pairing.

These are consequences of existing Library definitions and lemmas. No
group-theoretic assertion, actual-apartment existence or unconditional
equal-length conclusion is asserted.
