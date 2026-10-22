# Chain representatives for ordinary homological transfer

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

This pair develops the representative formula for the ordinary transfer
constructed on Mathlib's standard resolution. A homogeneous generator is
sent to the sum over left cosets of its inverse-coset translate, followed
coordinatewise by the subgroup coordinate map. Both the coefficient action
and the scalar on the homogeneous generator are retained.

The existing bar-to-standard isomorphism then gives an explicit formula on
each inhomogeneous generator. The tuple `transferTuple` consists of
successive differences of the subgroup coordinates of the translated
partial-product tuple. The initial subgroup coordinate is `1`, so the
coefficient of the summand is exactly the inverse representative acting on
the original coefficient. This is a formula for the constructed chain map,
not a definition of the transfer on cohomology.

These are internal representative calculations from `HomologyTransfer` and
`StandardChains`, following the homological transfer in Serre, *Local
Fields*, Greenberg translation, GTM 67 (1979), Chapter VII section 7,
printed pages 118–119 (PDF pages 124–125). Registered source:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The comparison with negative Tate restriction remains a separate obligation.
