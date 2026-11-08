# Elementary lifts of Hermitian middle reflections

This internal continuation of `HermitianRootReflections` uses the established
coordinate model and field algebra to construct actual elementary Levi
elements. The coefficient field and finite middle-index universes are
independent. No characteristic, anisotropy, nondegeneracy or
nonidentity-involution restriction is imposed.

`Parameters.traceZero H s hs` is the root parameter `(0,s)`, where
`hs : s + bar(s) = 0`. Its trace equation follows from the zero vector.
For `s≠0`, `traceZeroReflection H s hs hne` is its existing three-root
reflection and lies in `elementarySubgroup H`. The specialized value
formula identifies its matrix as

    [ 0          0     s ]
    [ 0          I     0 ]
    [ 1/bar(s)   0     0 ].

The product of this element with the trace-zero reflection for `bar(s)` is
the identity. The proof evaluates the nine block types and uses the
involution identity and nonvanishing of `s`. The inverse theorem then follows
from this product identity in the general linear group.

`leviMatrix a T` is the matrix with diagonal blocks `a`, `T`,
`1/bar(a)` and all off-diagonal blocks zero. It is defined for arbitrary
scalars and middle matrices; the definition alone asserts no invertibility.
For a root parameter `x` with nonzero scalar `z`, `reflectionLeviElement`
is the actual invertible product

    reflectionElement x * (traceZeroReflection H s hs hne)⁻¹.

Closure under multiplication and inversion proves membership in
`elementarySubgroup H`. `reflectionLeviElement_val` identifies its
matrix with

    leviMatrix (z/s) (reflectionMiddle x),

whose bottom diagonal entry is `bar(s)/bar(z)`. The proof substitutes the
pure-reflection inverse and the two reflection value formulas, evaluates
block entries, and normalizes field products. Elementary containment already
places each such lift in the special unitary subgroup.

For a unit `r` fixed by the involution, `r*s` is again nonzero and
trace-zero. Using the parameter `(0,r*s)` makes the middle reflection the
identity and the top coefficient `(r*s)/s=r`. Comparison with the existing
`diagonalEmbedding` proves
`diagonalEmbedding_mem_elementarySubgroup_of_traceZero`. The resulting
matrix is `diag(r,I,1/r)`.

All conclusions using a pure reflection require the supplied nonzero
trace-zero scalar. This module does not assert that such a scalar exists for
every involution. It supplies explicit Levi lifts and fixed-unit diagonals;
generation of arbitrary middle unitary transformations, group-scheme
classification and the unrestricted local Kneser–Tits proposition remain
separate obligations.
