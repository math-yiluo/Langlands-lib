# Compact integration of positive forms

Authors: Worker 117 and Worker 15.

Evaluation local constancy reuses the public theorem
`Langlands.Induction.eval_isLocallyConstant` from
`Langlands.Representation.Induction.CompactQuotientProof`.

This constructor does not prove the closed normalized-induction unitarity target.
The generic constructor `Induction.integralInvariantPositiveForm` integrates
a supplied positive Hermitian core over a subgroup `K`. Its explicit hypotheses
are full support of the measure, the factorization `G = P K`, integrability of
each scalar pairing, and invariance of that integral under every ambient right
translation. No topology or completeness on the inducing carrier is used.

Smooth induced evaluation is locally constant by its uniform open stabilizer,
so every scalar pairing and its real part are locally constant. The constructor
uses the integral identities for conjugation, addition, and scalar multiplication
to obtain the Hermitian core laws. Nonnegativity follows by integration. If the
diagonal integral is zero, the nonnegative real diagonal integrand vanishes
almost everywhere. Its continuity and the full support of the measure give
pointwise vanishing on `K`. Definiteness of the input core and covariance of the
actual induced functions then give vanishing on all of `G = P K`.

This is an internal derived step in the compact-picture argument of Casselman,
*Introduction to the theory of admissible representations of p-adic reductive
groups* (1995), sections 2.4 and 3.1, especially Proposition 3.1.4, literature ID
`casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
It proves no existence of the scalar functional. That analytic input and the
finite external tensor positive form remain separate prerequisites.

The general constructor only needs a subgroup and a measure positive on every
nonempty open set. Compactness and the Haar property are not assumed by this
constructor, because integrability and full support are stated directly. Its
inducing representation `τ` need not preserve the supplied core `b`; the scalar
right-translation identity is required for every pair of functions and every
ambient group element. This separation allows the normalized inducing action,
which scales the original form, to be used later. No new representation,
unitarizability predicate, or certificate is introduced.

`pairing_isLocallyConstant` exposes the local constancy of any supplied core
pairing of two actual smooth induced functions. The field universe of the
group and the carrier universe remain independent throughout. The local core
instance in the definiteness proof supplies only algebraic core lemmas; no norm
or topology is installed on the inducing carrier.

The source cited above is the retained original at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
Sections 2.4 (pages 26–27) and 3.1 (pages 32–33) motivate the scalar functional
and compact pairing. This implementation uses the Bochner integral only for
complex scalar functions, and its almost-everywhere argument is a derived
implementation of positivity and definiteness, rather than a transcription
of the source. The proof was adapted against pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
