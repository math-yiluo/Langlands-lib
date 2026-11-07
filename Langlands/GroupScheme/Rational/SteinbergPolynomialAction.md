# Finite polynomial action of the actual Steinberg product

This internal construction uses the actual additive polynomial matrices, supplied root maps, and rational simple-reflection representatives. It retains arbitrary fields and coefficient algebras, including nonreduced algebras. The common degree bound is one plus the maximum degree of all matrix entries, so the expansion has finitely many terms even when the representation has dimension zero.

`affineMatrix_eq_sum` expands the matrix over every coefficient algebra; `affineMatrix_mulVec_eq_sum` expresses the same action through the actual divided-power operators. These follow entry by entry from polynomial evaluation and the coefficient definitions. No factorial is divided out and no rational-point density is used.

`coordinates_affinePoint` compares the affine parameters with the existing global-section coordinates. The universal parameter is the identity point of affine space. `steinbergPolynomialMatrix` is the ordered product of the actual root polynomial matrices evaluated in distinct variables and the actual rational representative matrices extended to the polynomial ring. The affine matrix factorization evaluates the supplied ordered scheme morphism, with exactly its original ordering and supplied families.

`steinbergPolynomialMatrix_aeval` identifies evaluation of this polynomial matrix with the actual matrix at the supplied Steinberg product over every coefficient algebra. Its proof maps the ordered product through the evaluation homomorphism, applies the existing evaluation formula for each additive representation, and evaluates each constant representative matrix. Specializing to the polynomial coordinate algebra and its universal variables gives `steinbergPolynomialMatrix_eq_affineMatrix`.

`steinbergRestriction_traceClassFunction` states that the actual invariant trace character restricts to the trace of this polynomial matrix. It follows by evaluating the existing trace coordinate at the universal Steinberg point and applying the preceding matrix identity.

The provenance is internal: these statements derive from the existing actual representation, vector-group, root-product, trace, and restriction constructions. No external structure theorem or character formula is used.

This pair supplies a finite polynomial model for the character calculation. It does not establish highest-weight existence, the triangular character formula, generation of the invariant algebra, or the quotient isomorphism.
