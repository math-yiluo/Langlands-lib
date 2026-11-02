# Reversed duals of contractible and acyclic complexes

Author: Worker 1015.

This internal supporting construction uses the reversed dual defined in
`FiniteFreeReversedDual.lean`. For any commutative ring, integer `g`, and
cochain complex `C`, `reversedDualContraction` transposes a contracting
homotopy of `C` to a contracting homotopy of `reversedDual g C`. Its
component in degrees `i,j` is the dual of the original homotopy component
in degrees `g-j,g-i`. Transposing the original homotopy identity gives
the required identity, with the two summands exchanged.

`isZero_homology_reversedDual_of_contraction` applies the equality of
homology maps induced by homotopic maps to the identity and zero. Their
equality says that every homology object of the reversed dual is zero.

`isZero_homology_reversedDual_of_acyclic` assumes that `C` is bounded
above, has projective terms, and is acyclic. Mathlib's
`CochainComplex.isKProjective_of_projective` and
`CochainComplex.IsKProjective.homotopyZero` then supply a contracting
homotopy of `C`, so the preceding result applies. No finite-generation
hypothesis is needed for this conclusion.

The construction and supporting results are internal consequences of
Mathlib's homotopy and K-projective APIs. They make no assertion about
finite-length homology, localization, or the punctual complex theorem.
