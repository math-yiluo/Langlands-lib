# Fixed vectors from schematically dense rational points

The proof implements the schematic-density step of Milne, *Algebraic Groups*
(2017), Corollary 14.10, using the fixed-vector definition of unipotence.

Let `G` be an affine group scheme over a field `k`. Assume that any closed
immersion into `G` through which every `k`-point factors is an isomorphism.
If a vector `v` is fixed by all rational matrices of a representation `ρ`,
`isFixedVector_of_schematicallyDense` shows that `ρ.IsFixedVector v`.

A global function `f` vanishing at each rational point defines a principal
ideal sheaf on `G`. Containment of that ideal sheaf in the kernel of each
rational point gives a factorization through the corresponding closed
subscheme. By the density hypothesis its inclusion is an isomorphism. The
ideal sheaf is therefore zero, so its ideal of global sections is zero and
`f = 0`.

By `MatrixRepresentation.isFixedVector_iff_universal` it suffices to check the
fixed-vector equation for the universal matrix on `G`. Its coordinates minus
the scalar extensions of the coordinates of `v` vanish at each rational point,
by the scalar and matrix evaluation lemmas of `CentralIntersection` and the
assumed rational fixedness. Applying the vanishing argument to each of these
coordinate differences proves the equation.
