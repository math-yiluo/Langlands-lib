# Exact integral-point images of scaled vector models

`principalVectorLattice R K n t` is the `R`-submodule of `Fin n → K`
consisting of vectors with coordinates `t * algebraMap R K a_j` for some
`a : Fin n → R`. This definition permits every scalar `t : K`, including
zero, and every finite dimension. Closure follows from addition of the integral
coefficients and multiplication of those coefficients by elements of `R`.

For a domain `R` with fraction field `K`, the scaled vector model with generic
scaling factor `t : Kˣ` sends an integral section with coordinates `a_j : R`
to the generic vector whose coordinates are `t * algebraMap R K a_j`.
Consequently, its exact integral-point image in the generic vector group is
the principal lattice `t · Rⁿ`. The theorem
`scaledVector_mem_integralPoints_iff_mem_principalVectorLattice` identifies
membership in the actual integral-point image with membership of the canonical
coordinate vector in this explicitly defined submodule.

The proof computes the actual integral-point map defined by restricting
a section along `Spec K → Spec R`, using the pullback projection and the
canonical vector-group base-change isomorphism, and then applying the supplied
scalar generic identification. Naturality of `ΓSpecIso` identifies the coordinate
change with the specified ring homomorphism. Surjectivity of the section-coordinate
equivalence supplies an integral section for every vector in the lattice.

These are internal consequences of the polynomial vector-group coordinates,
their base change, and the actual integral-point map. They provide the image
calculation for the additive scaled models of Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Section C.2, printed pp.697–698 /
PDF pp.728–729, source `kaletha-prasad-2023-bruhat-tits-new-approach`.
No comparison with an arbitrary supplied root filtration is asserted here.
