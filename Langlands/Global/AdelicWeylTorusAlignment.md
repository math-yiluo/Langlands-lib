# Aligning the split tori of Weyl-related parabolics

`WeylTorusAlignmentStatement` concerns the actual maximal split tori used in two
verified parabolic root presentations. Given the Weyl conjugation witnessed by
`w` and `c`, it supplies a rational point `z` of the source Levi and a torus
isomorphism. Inverse conjugation by `w * z` restricts to that isomorphism.

`ParabolicRootPresentation.exists_leviTorusLift` uses the all-test standard Levi
identity to factor each presentation torus through its specified Levi and retain
maximality. `weylTorusAlignment` carries the target factor to the source Levi
along `c` and applies the Library's rational conjugacy of maximal split tori
there. The inverse of that conjugating point is the right factor in the new
representative. The equality of actual inclusions follows from the formula for
inverse conjugation by a product and naturality of inner automorphisms.

This is an internal reduction from the Library's `IsWeylConjugation` and
`ParabolicRootPresentation` data.
