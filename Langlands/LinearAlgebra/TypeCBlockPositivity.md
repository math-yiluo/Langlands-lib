# A positive functional on repeated type C restrictions

This internal integer calculation supplements `TypeCBlockWeights`. The additive
functional `height` pairs the block-coordinate vector with `(r, r-1, ..., 1)`.
A nonzero repeated weight is a single coordinate vector; its height is
`r - floor(i / degree)`, and weights outside the first `r` blocks have height
zero. At a nonzero boundary between consecutive weights, their difference has
height one. The final long simple root is twice a repeated weight, so its
height is positive whenever that weight is nonzero.

Consequently, every numbered simple restriction is zero or has strictly
positive height when `degree > 0`. This conclusion needs no bound relating the
number of blocks to the ambient rank. The proof is elementary integer and
finite-sum arithmetic using the Library's existing boundary criterion. It does
not assert that these coordinates are the restrictions of an actual group;
that comparison must be supplied separately.
