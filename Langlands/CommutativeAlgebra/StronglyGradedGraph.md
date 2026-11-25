# Strong grading from a surjective action graph

Internal derived commutative algebra for affine quotients by central
multiplicative-type subgroups. Let A be an
algebra over any commutative ring R and let a coefficient grading by any abelian
group M be given by an R-algebra homomorphism A → A[M]. The graph coordinate
homomorphism A tensor_R A → A[M] sends a tensor b to a times the coaction of b.
If this homomorphism is surjective, the grading is strong in the finite
dual-family sense of `StronglyGraded`.

For each degree m, take a preimage of the monomial with coefficient 1 and write
it as a finite sum of simple tensors. Its degree-m coefficient expresses 1 as
a sum of products a_i p_m(b_i). Project this equality to degree zero.
Multiplication by a homogeneous element shifts projections, so this becomes
a finite partition of unity by p_{-m}(a_i) p_m(b_i), as required. No field,
finite-generation, reducedness, or smoothness assumption is used.

Provenance: an internal coefficient proof of the strong-grading step in SGA 3,
Exposé VIII, Gille–Polo recomposition of 8 November 2009, §§4–5, especially the
proof of Theorem 5.1. Registered source `sga3-expose-viii-gille-polo-2009`,
SHA-256 `06e43e0571d411cc5579975778fcc03c8ecaa67189248d1a053e61dc653af510`.
The module does not construct a scheme action or assert that a given geometric
action has a closed graph; those adapters are not part of this module.
