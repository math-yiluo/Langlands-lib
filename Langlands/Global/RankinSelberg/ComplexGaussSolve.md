# Smooth Gauss coordinates for complex matrices

The pivot domain is defined by nonvanishing determinants of the trailing
principal blocks. It is open by continuity of the determinants. For
each column, solve the lower equations with the inverse of its
trailing block. This is the prescribed column solve. Block extraction
is linear and matrix inversion is smooth at invertible blocks, so the
strictly lower coordinates of the solution vary smoothly on the
pivot domain.

The solution is lower unitriangular and right multiplication by it
annihilates every strictly lower entry. For an invertible input this
gives an upper triangular group element and an actual Gauss
factorization. Conversely, an upper triangular times lower unipotent
factorization has invertible trailing blocks. The lower block has
determinant one and the upper block has nonzero diagonal. Uniqueness
of the column solve recovers the inverse of the lower factor.
