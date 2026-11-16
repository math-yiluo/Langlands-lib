# Fppf locality of actual subgroup comparison squares

This internal module derives a gluing criterion from the published all-test
`LocalGroupIso` interface and its fppf descent. It is used for the coordinate
torus clause of relative pinned comparisons. It does not prove local pinning
normalization or construct a root-datum equivalence.

Let `i : A → G`, `j : B → H` be group-scheme homomorphisms over an arbitrary
scheme, with `j` a monomorphism on the underlying relative schemes, and let
`e : G ≅ H`. A local subgroup isomorphism whose square with `i`, `j` and `e`
commutes at every test and cover point is independent of the cover point:
cancel `j` in the two squares. The resulting family descends on any flat,
surjective cover locally of finite presentation. Its ambient square is checked
on points after the fppf projection, where the descent recovery equation gives
the original local square. The square determines the subgroup isomorphism
uniquely by the same monomorphism cancellation.

An actual isomorphism of the pulled-back subgroup schemes with the pulled-back
ambient square gives exactly such an all-test family. The theorem
`existsUnique_iso_of_baseChange_square` therefore descends the actual subgroup
square and gives uniqueness. These results do not assume that a scheme is
affine, connected, nonempty, or quasi-compact and do not select a global
constant map of coordinate lattices.
