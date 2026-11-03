# Proof that Hilbert–Schmidt products are trace class

`Langlands.Analysis.OperatorIdeals.hilbertSchmidtProductTraceClass`
proves `HilbertSchmidtProductTraceClassStatement` for rectangular maps
between complete complex inner-product spaces in independent arbitrary
universes.

For an endomorphism A let L be its positive left modulus sqrt(A A*).
Self-adjointness of L, its square identity, and the adjoint norm
identity give `‖A* x‖ = ‖L x‖`. Co-restrict A* to the closure S of its
range. `LinearMap.extendOfNorm` descends L through that dense map and
extends it to S. Composing with the orthogonal projection onto S gives
a bounded T satisfying L = T A*. Taking adjoints gives L = A T*.
This construction repeats the private range-extension argument of
`LeftModulusFactorizationProof`, with the two norm-equal maps reversed;
it does not import or expose that module's private helper.

Apply this to A = C B and put U = T*. The Hilbert–Schmidt
precomposition law shows B U is Hilbert–Schmidt. The absolute-diagonal
part of `hilbertSchmidtProductTrace` applied to B U and C gives
absolute summability of the complex diagonal of C (B U) in a chosen
subset-indexed Hilbert basis of E. This composition is L.
Mapping its convergent diagonal sum through the real-part map supplies
the witness required by `IsTraceClass (C.comp B)`.

The statement Markdown gives the original Exercise 9.2 and the precise
rectangular and nonseparable extension. The proof assumes neither
trace-class ideal closure nor complex trace basis independence. It uses
no compact spectral theorem or assumed polar decomposition.
