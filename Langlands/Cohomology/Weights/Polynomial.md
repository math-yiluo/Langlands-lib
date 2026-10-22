# Polynomial weight factors

Author: Worker 41.

This module constructs the complex polynomial factor that retains all roots of
a specified integral weight, counting multiplicity. It is an algebraic
prerequisite for the separation of cohomological degrees in Kottwitz's proof.
It does not state or assume the existence of Shimura cohomology or a compatible
Galois family.

For a natural number \(q\) and integer \(w\), `radius q w` is
\(q^{w/2}\), using the real power function. Applications use \(q>1\).
`HasComplexWeight q w z` means \(|z|=q^{w/2}\) in this one complex
realization. `IsWeilNumber q w z` additionally requires algebraicity over
\(\mathbf Q\) and that every complex zero of the minimal polynomial of \(z\)
over \(\mathbf Q\) has this absolute value. Thus a condition at one complex
embedding is distinguished from the condition at every algebraic conjugate.
Negative weights are allowed.

`HasComplexRootsOfWeight q w P` quantifies over the roots of a complex
polynomial. It does not require the polynomial to be monic or algebraic; any
use needing those properties must supply them separately. In contrast,
`IsPurePolynomial q w P`, for a polynomial over an actual number field \(L\),
requires monicity and the Weil-number condition for every root after every
embedding \(L\to\mathbf C\). The polynomial \(1\) is allowed, which represents
a zero-dimensional cohomological summand.

`complexWeightFactor q w P` is the product of \(X-z\) over the submultiset of
`P.roots` satisfying `HasComplexWeight q w`. It is constructed directly using
Mathlib's polynomial roots and multiset operations. It retains multiplicities.
`complexWeightComplement` uses the complementary submultiset. These
constructions are noncomputable because the root and absolute-value equality
operations use classical mathematics.

The intrinsic laws prove that both constructions are monic, identify their
root multisets, and show that their product is \(P\) when \(P\) is monic.
The proofs use factorization over the algebraically closed field \(\mathbf C\),
not an assumed root decomposition. The weight factor is idempotent, respects
products of nonzero polynomials, and respects all natural powers. For \(q>1\),
strict monotonicity of real exponentiation shows that a complex number cannot
have two different integral weights. Consequently a polynomial all of whose
roots have one weight has factor \(1\) at every other weight. These are
construction laws, not the cohomological trace identity or Taylor's theorem.

## Source correspondence

The original source is Robert E. Kottwitz, *On the lambda-adic representations
associated to some simple Shimura varieties*, Inventiones Mathematicae 108
(1992), 653–665, registered as
`kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
Worker 41 read the complete thirteen-page original through a local extraction
and visually checked printed pp. 657 and 664.

Theorem 1(b), p. 657, uses eigenvalues of weight \(i+w(\xi)\), allows
general irreducible algebraic coefficient systems \(\xi\), and separates
\(P(\pi_p,E_v)\) into monic factors of those weights. Section 6, p. 664,
uses their distinct absolute values to prevent cancellation in the alternating
characteristic rational function. The present root-filter construction is a
derived implementation of the complex factor in that argument. The source
does not introduce our Lean names or this particular multiset implementation.
The two displayed polynomial constructions here are over \(\mathbf C\).
Their descent to the source's coefficient number field \(L\) remains a
separate obligation; it is not inferred merely from one complex absolute value.

## Dependencies and remaining boundaries

The only imports are from the prepared Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment, artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`. No pending project definition or
unproved project theorem is imported.

This module supplies actual weight predicates and complex factors. It supplies
neither the unitary similitude group, its Shimura variety, its general
coefficient sheaf, nor the Hecke and Galois actions. In particular, it does
not define an arbitrary object with those names or package their conclusions
as record fields. The full Kottwitz statement must retain the reflex field,
sufficiently small level, all three bad-prime conditions, geometric
Frobenius, the coefficient-prime exclusion, and the signed cohomological
multiplicity. The compatible-family, Clozel transfer and parity removal,
Taylor multiplicity removal and Hodge–Tate hypotheses, and Harris 1998/1999
statements remain obligations of the assigned task. This prerequisite alone
does not complete that task. Compilation does not establish independent
mathematical acceptance.
