# Full Tate images of reverse multiplication factorizations

Author: Worker 1730.

This is an internal algebraic consequence of the published full Tate limit and
the coordinate-division result in `FullEvaluationKernel`. It applies to any two
commutative group schemes `G`, `H`, any test scheme `T`, and actual homomorphisms
`f : G → H`, `r : H → G` with both composites equal to multiplication by the
same positive integer `n`. No external source is cited.

`map_multiplication_apply` checks at every torsion coordinate that the Tate map
of multiplication by `n` is natural multiplication by `n`.
The two composite lemmas therefore give `T(r) T(f) = n` and
`T(f) T(r) = n` on the actual full coherent-family groups.

The definition `fullReverseKernelEquiv` is the additive equivalence from `T(H)`
onto the kernel of evaluation at `n` after `T(f)`. Its forward map is exactly
`T(r)`. The second composite identity and level annihilation place this image
in the kernel and prove injectivity using full Tate multiplication injectivity.
If `x` belongs to the kernel, the full coordinate-division lemma gives `y`
with `n • y = T(f) x`. Apply `T(r)` and the first composite identity to obtain
`n • T(r) y = n • x`, then cancel positive multiplication in `T(G)`.
This proves surjectivity onto the kernel.

`exists_map_reverse_iff` rewrites the result in the form needed by the lattice
realization proof: a full integral `x` lies in the image of `T(r)` exactly when
its `n`-coordinate is killed by the level map of `f`.

The module constructs no quotient, reverse homomorphism or rational isomorphism.
Those are inputs to this algebraic comparison. It requires no finite-rank,
surjectivity-on-geometric-points, étaleness, or base invertibility premise.
