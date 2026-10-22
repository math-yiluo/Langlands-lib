# Canonical comparison from ordinary to Tate cohomology

Author: Worker 45.

`ordinaryToTate A n` is an actual linear map from Mathlib's
`groupCohomology A n` to `tateCohomology A n` for every natural number `n`.
In degree zero, Mathlib's `H0Iso` identifies the ordinary group with invariant
vectors, and the published `zeroClass` maps an invariant vector to its class
modulo the image of the actual group norm. In positive degrees, the map is
the inverse of Mathlib's existing `TateCohomology.isoGroupCohomology`.

The maps form the natural transformation `ordinaryToTateNat` in coefficient
representations. Its degree-zero naturality certificate combines naturality
of `H0Iso` with the published naturality of `zeroClass`; positive naturality
is part of Mathlib's comparison isomorphism. The accompanying formulas
identify invariant representatives and the degree-zero kernel. Surjectivity
follows from the norm quotient at zero and the comparison isomorphism in
positive degrees.

This is an internal assembly of existing, proved interfaces. The underlying
ordinary/Tate identification and norm quotient are described in Serre,
*Local Fields* (1979), VIII section 1, printed pages 127–129 (PDF pages
133–135), source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The construction uses a finite group and an arbitrary commutative scalar
ring, with both in arbitrary common universe `u`; it applies in particular
to the lifted integral scalar ring. No flatness assumption is required.

This module supplies a comparison interface for subsequent ordinary cup
statements. It does not define an ordinary cup product or assert cup or
connecting-map compatibility.
