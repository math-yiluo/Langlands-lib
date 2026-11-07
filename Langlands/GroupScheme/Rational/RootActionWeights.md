# Root-group coefficient operators and actual torus weights

Author: Worker 1284. Provenance: internal. This pair derives coefficient operators between actual torus weight spaces from the supplied normalized-root conjugation law. It uses the existing actual additive-group polynomial matrix and its divided-power operators. No representation-theoretic existence or classification theorem is assumed.

Let `p` be a supplied split pinning of an actual affine group scheme over an arbitrary field `k : Type u`, let `a` be a simple root and let `x : p.NormalizedRootParametrization a`. For any finite matrix representation `rho` of that group, write `B_m` for `AdditiveDividedPowers.coefficientMatrix (rho.restrict x.hom) m`. These are the degree coefficients of the actual polynomial matrix of the restricted additive-group representation; they are not freely supplied endomorphisms. The corresponding `dividedPower` is `Matrix.toLin' B_m` by the imported theorem `dividedPower_eq_toLin`.

The first two lemmas compare the additive scalar parameter and the character value on affine tests with the existing global-section versions. `affinePoint_eq_scalarPoint` uses the corepresented affine/global-section comparison. `charValue_affine` uses the global-sections/spectrum isomorphism. They identify the exact supplied root law with `affinePoint_conjugation` over every commutative coefficient algebra. Applying the actual representation and cancelling the inverse torus matrix proves `affineMatrix_root_commutation`.

`coefficientMatrix_root_commutation` proves, for every coefficient algebra `A` and every actual torus point `t`,

`rho(t) * B_m,A = alpha(t)^m * (B_m,A * rho(t))`.

Here `B_m,A` denotes entrywise scalar extension of `B_m`, and `rho(t)` is the matrix of the actual representation restricted to the supplied torus. The proof evaluates root commutation over `A[X]` at the universal polynomial parameter `X`, extending `t` along the constant inclusion. Naturality identifies the constant torus matrix and character value. Extracting degree `m` gives the identity. The helper `coeff_aeval_C_mul_X` is proved by monomial induction and supplies the factor `alpha(t)^m`. Thus the proof does not use density of field-valued parameters or division by factorials.

`dividedPower_mem_representationWeightSpace` applies this covariance at the universal affine point of the actual torus. If `v` belongs to `p.representationWeightSpace rho lam`, its degree-`m` root coefficient belongs to the actual weight space at `lam + m • p.rootDatum.root a`. The universal character equation defining the original weight space, matrix-vector associativity and multiplication of character units prove precisely the universal character equation for the shifted weight space. The imported character-space evaluation theorem then gives its usual meaning over every commutative coefficient algebra, including nonreduced algebras.

`weightRaisingOperator` packages that same divided-power operator as a linear map from the original weight subspace to the shifted one; its underlying-vector equation is proved. `dividedPower_eq_zero_of_weightSpace_eq_bot` proves that the coefficient vanishes when the shifted weight space is zero.

No algebraic-closedness, simple-connectedness, characteristic restriction or irreducibility assumption occurs. The result concerns the supplied simple-root map; its torus-equivariance field suffices for the argument, and the derivative field is not used. This pair does not construct fundamental representations, prove invariant generation or the triangular character restriction formula, or establish the canonical quotient isomorphism. Those remain separate obligations of the host task.
