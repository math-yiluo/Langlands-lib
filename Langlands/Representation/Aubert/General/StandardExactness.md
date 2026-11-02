# Exactness with the terminal cokernel retained

Internal target interface and intrinsic construction laws by Worker 194.

`IsExactBeforeTerminal A I` requires the kernel of the actual signed
differential to equal the actual incoming image at each removed-root degree
`k < |S| - |I|`. At degree zero the incoming image is zero. Under
`P(S) = G` and `U(S) = 1`, `initialDifferential_injective_of_exact` therefore
proves injectivity of the canonical first arrow from `A` when the retained
degree is positive. It uses the constructed initial equivalence and the
linear-map kernel criterion, with no finite-length assumption.

At terminal degree `|S| - |I|`, the constructed projection has the proved
incoming-image kernel and is surjective. These quotient laws do not require
the earlier exactness predicate. The predicate imposes no condition on the
outgoing differential at terminal degree and does not assert that `A#`
vanishes. If `I = S`, including an empty root set, the exactness predicate
has no conditions; the construction retains the degree-zero quotient.

This is the exactness convention in Aubert's 1996 erratum, printed p.4687,
display (*), and the retained-cokernel definition on p.4690. It is a generic
interface for the actual subgroup-family complex. No theorem here asserts
that an arbitrary nested family satisfies corrected Theorem 3.6. The
representation-theoretic assertion for every smooth object of `Alg({I})`
will be a separate proposition target, specialized eventually to the actual
standard-subset realization. The corrected two-sided support argument and
the other unproved general representation-theoretic inputs remain necessary
for its proof.
