# Clifford lifts of determinant-one isometries

Over a commutative ring, a Clifford lift is a pair of a Clifford unit and a determinant-one linear automorphism. The unit is fixed by the grade involution, has reversion norm one, and intertwines the vectors with their images under that automorphism. The pairs form a subgroup under componentwise multiplication. The determinant is Mathlib's `LinearEquiv.det`. It is the usual determinant for a finite free module and is one for every automorphism of a module without a finite basis.

When `2` is invertible, the grade-involution condition is equivalent to membership in the even Clifford part and the action preserves the quadratic form. Under the same invertibility hypothesis, a linearly ordered orthogonal basis of unit values makes the action kernel exactly the scalar square roots of unity.

Over a field, assume the form is finite dimensional, its polar pairing is nondegenerate, and `2` is invertible. An even reflection word lifts to this group if and only if its product of quadratic values is a square. Over an algebraically closed field every determinant-one isometry then lifts. This construction records the coefficient-group part of the spin covering and uses the spinor norm of the exact sequence in Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.11, p. 99.
