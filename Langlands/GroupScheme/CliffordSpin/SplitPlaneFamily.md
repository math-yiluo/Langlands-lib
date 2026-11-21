# A Laurent family through the scalar Clifford kernel

`scalarPoint` is the affine Clifford lift defined by a scalar square root of unity. Its Clifford unit is the scalar and its matrix is the identity. `evaluateLaurent` specializes a Laurent polynomial at a unit of the coefficient field.

`exists_laurentPoint_through_scalarKernel` constructs a point of the actual Clifford scheme over `K[T,T⁻¹]` for every algebraically closed coefficient field `K` and every regular scalar form of dimension at least two. A hyperbolic pair `e,f` is chosen over `K` with both quadratic values zero and polar pairing one. After extension to the Laurent algebra, `e+f` and `Te+T⁻¹f` both have quadratic value one. Their Clifford product with its even reflection action gives the Laurent point. At a square root of unity `t`, the second vector specializes to `t(e+f)`, so the product specializes to the scalar `t`. The Clifford unit determines the vector action because the vector inclusion into the Clifford algebra is injective.

The construction uses the same Clifford reflection and central kernel formulas as Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99. The Laurent family is a derived geometric calculation on the affine coordinates.
