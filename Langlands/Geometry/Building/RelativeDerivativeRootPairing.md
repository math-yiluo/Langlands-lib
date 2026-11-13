# Full derivative root pairings on the actual relative-root span

Worker 227. Internal transport construction for Task 6205. Assume a split
torus, a rank-zero-compatible affine root system on an affine space under
the actual reduced translation space, and equality of its full derivative
set with the range of actual relative-root forms. No root is discarded.

`relativeDerivativeRootEquiv` identifies the rational relative-root span
with the full rational derivative span using `relativeRootFormEquiv` and
the assumed equality of derivative sets. `relativeDerivativePairing`
transports the full rational derivative root system along the inverse of
this equivalence and its dual. Its pairing is evaluation on the actual
relative-root span, it remains crystallographic, and its root image in
the rationalized character lattice is exactly the image of all actual
relative roots. Every indexed root-coroot pairing is unchanged.

The derivation uses only the published apartment and relative-root
constructions, the rational evaluation comparison, and Mathlib transport
by linear equivalences. It asserts no reducedness or symmetry and gives
no proof of splitting or the host affine-diagram theorem. Empty systems
and independent field and affine-space universes are permitted.
