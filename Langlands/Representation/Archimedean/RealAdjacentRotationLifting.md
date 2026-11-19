# One-sided lifting for two adjacent rotations

`RealAdjacentRotationLiftingStatement` concerns a finite-dimensional complex
vector space with adjacent generators `a`, `b`, their commutator `c`, and the
commutator identities `[b,c]=a` and `[c,a]=b`. Both generators have finite
integer-mode decompositions in the convention of `RealOrthogonalUncertainty`.
Fix a positive cutoff `N` and write `P_H` for the degree-`H` differential
tail polynomial. If `P_H(-I • b)v` has zero `a`-modes at every `j ≥ N+H`,
there is a vector in the kernel of `P_H(-I • b)` with the same `a`-modes
as `v` at every `j ≥ N`.

The proof derives the result from the single-string theorem of
`RealAdjacentWeightStringLifting` and the coefficient bound of
`RealAdjacentFourierBand`. The commutator identities imply that
`e=b-I • c` raises `a`-modes by one and `f=-(b+I • c)` lowers them by one.
Start with a nonzero vector `u` in a highest supported mode `J`. It is
killed by `e`. On the vectors `u_k=f^k u`, the identity
`[e,f]=(-2*I) • a` gives `e u_{k+1}=(k+1)(2J-k)u_k`. There are only
finitely many modes, so some `u_k` vanishes. Any first vanishing at
`k+1` forces `k=2J`. The vectors up to that index have distinct modes and
span a subspace of dimension `2J+1` invariant under both generators.

In a minimal nonzero invariant subspace, this string spans. Applying the
same argument with `a` and `b` exchanged and `c` negated gives a second
string of the same dimension. Its top mode is also `J`, so the normalized
operator `-I • b` has every integer eigenvalue from `-J` to `J`. The first
string gives mode spaces of dimension at most one and injective raising
below `J` by the displayed recurrence. These are the hypotheses needed
to apply the single-string lifting theorem to the minimal subspace.

For an arbitrary nonzero input, choose a common invariant subspace of
least positive dimension. Polynomial interpolation expresses each mode
projection as a polynomial in its generator, or the zero map outside
the finite support. The modes therefore restrict to the subspace and
descend to the quotient. Induction on dimension gives a lift in the
quotient. To obtain a representative in the polynomial kernel, take any
representative and retain just its `b`-modes at roots of `P_H`. The other
modes were already zero in the quotient.

The high `a`-modes of the residual lie in the invariant subspace. Sum them
to obtain a vector in that subspace. The discarded modes are below `N`,
so the degree bound implies that their polynomial image has no modes
at or above `N+H`. This gives the polynomial-image hypothesis for the
vector in the subspace. Add its single-string lift to the kernel
representative from the quotient. The resulting kernel vector has the
required high modes. The zero input has the zero lift.
