# Actual general linear points and the matrix-units topology

Author: Worker 94.

This internal comparison equips the existing multiplicative equivalence
`GeneralLinear.affinePointsEquiv` with its two continuity proofs. The group
scheme is the published `GeneralLinear.groupScheme n R` with coordinate algebra
presented by entries of a matrix and its inverse, subject to both inverse
identities. The coefficient ring is any topological commutative `R`-algebra `S`;
no topology on `R` and no continuity of its scalar map are required. The source
carries the actual global-function evaluation topology and the target is the
published `GL n S`, namely the matrix unit group with its units topology.

The two coordinate identities compare the published global-section point
comparison with the affine comparison via the canonical global-sections/spectrum
isomorphism. Thus `entrySection` and `inverseEntrySection` evaluate to matrix
entries and inverse entries. They imply continuity to the matrix unit group,
whose topology records both a matrix and its inverse. This direction requires
only a topology on `S`.

For the reverse direction assume `IsTopologicalRing S`. A coordinate-algebra
element is represented by a polynomial. Polynomial induction proves continuity
of its classifying value, using continuous addition and multiplication and the
continuous matrix and inverse-matrix entries. Naturality of the global-sections
isomorphism identifies this value with evaluation at the spectrum of the
classifying map, which is the published inverse affine point comparison.
The evaluation-topology universal property then proves its continuity.
`affinePointsHomeomorph` retains exactly the existing multiplicative equivalence.
All finite matrix index types, including the empty index type, are covered.

This is an internal consequence of the published coordinate presentation and
Getz–Hahn, *An introduction to automorphic representations* (2024), §2.2,
Theorem 2.2.1, canonical injection (2.8), and Proposition 2.2.2, printed pp.51–54.
Registered source `getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
This unit proves the topology comparison for actual coefficient points;
adelic specializations, quotient comparisons and function spaces are separate
constructions.
