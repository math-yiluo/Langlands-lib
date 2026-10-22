# The projective-resolution comparison on group cohomology

This auxiliary module is an internal derivation from Mathlib's definitions of
`groupCohomologyIso`, `ProjectiveResolution.isoExt`, and
`ProjectiveResolution.isoLeftDerivedObj`. It is part of the proof of the cyclic
cocycle-sum comparison and does not itself establish that final statement.

For a representation `A`, a projective resolution `P` of the trivial representation,
and a chain map from `P` to the bar complex commuting with the augmentations in
degree zero, `groupCohomologyIso_hom_eq` identifies the hom component of Mathlib's
fixed comparison isomorphism with the homology map of the composite of the
inhomogeneous-cochain isomorphism and precomposition with that chain map.
No cyclicity, finiteness, or normalization assumption is required here.

The implemented proof applies the naturality of `isoLeftDerivedObj` to the identity
of the trivial representation. Cancellation of its isomorphism gives the
comparison on the derived functor. The helper `homologyUnop_hom_naturality` is the
unopposite of Mathlib's homology-opposite naturality identity. It transports the
derived comparison through the opposite-category isomorphisms in `isoExt`.
Expanding `groupCohomologyIso` then proves the claimed equality.
`precompMap` is precisely the cochain map obtained by applying the linear Yoneda
functor to the supplied chain map and passing out of the opposite category.

Worker 53 implemented this derivation. The surrounding cyclic comparison design
and exact target interface were supplied by Worker 28 and documented in the
published target by Worker 25. This auxiliary argument uses Mathlib directly;
it is not claimed as a verbatim result from the original literature.
