# Conditional scalar denominator cancellation

This derived supporting construction removes the factors of a nonzero actual
unramified regular scalar denominator that meet an open character region.
It explicitly assumes
`RationalUnramifiedLocalHypersurfaceDivisibilityStatement.{u}`.
That proposition remains a separate proof obligation. No premise is added to
the conditional standard intertwining statement.

## Actual scalar algebra and hypotheses

The actual results use an arbitrary nonarchimedean local field in universe
`u`, a connected reductive group scheme `G`, a supplied topology on its rational
points, and continuity of `rationalValuationImageProjection G`. The norm family
consists of all `rationalNormCharacters G`; the scalar algebra is the existing
evaluation-generated complex algebra `unramifiedRegularFunctions` for that
family. The parameter region `U` is any open subset of its full unramified
character space with the inherited compact-open topology. There is no
characteristic, splitness, quasisplitness, rank or nonemptiness restriction.

`continuous_unramifiedRegularFunction` first proves continuity for every
regular scalar for an arbitrary norm family. Algebra-adjoin induction starts
from continuous point evaluations of continuous complex-unit characters;
constants, sums and products preserve continuity.
`unramifiedRegularFunction_isUnit_eval_ne_zero` applies the point-evaluation
ring homomorphism to an algebraic unit.

## One factor

`rationalUnramified_cancel_irreducible` assumes that an irreducible scalar
`p` has a zero in `U` and that
`(p * b)(chi) * f(chi) = a(chi)` on `U`, with `f : U -> C` continuous
and `a,b` regular. At every zero of `p` in the region, this identity forces
`a` to vanish. The explicit local-divisibility premise then gives a regular
`c` with `a = p * c`.

Away from the zeros of `p`, scalar cancellation gives
`b(chi) * f(chi) = c(chi)`. The existing theorem
`rationalUnramifiedRegular_dense_nonzero_on_open` makes this locus dense in
`U`. Both sides are continuous, so `Continuous.ext_on` extends the equality
to every point of `U`, including the zeros of `p`.

## One denominator before all functions

`rationalUnramified_uniform_scalar_denominator` starts from any nonzero
regular scalar `b`. It produces a nonzero regular divisor `d` of `b`, with
`d(chi) != 0` at every point of `U`, such that the following property holds
for every continuous function `f : U -> C` and every regular scalar `a`:
if `b(chi) * f(chi) = a(chi)` everywhere in `U`, there is a regular scalar
`c` satisfying `d(chi) * f(chi) = c(chi)` everywhere in `U`.
The existential choice of `d` precedes both `f` and `a`.

The proof uses the existing unique factorization theorem for the actual scalar
algebra and `UniqueFactorizationMonoid.induction_on_prime`. A unit is already
nonzero at every evaluation. For a product `p * b`, if the prime `p` has a
zero in `U`, the one-factor result removes `p` and the induction hypothesis
handles `b`. If `p` has no zero in `U`, the induction hypothesis is applied to
the continuous function `p * f`; the resulting denominator is multiplied by
`p`. The zero case of the induction is excluded by the original nonzero
hypothesis. The argument also covers the empty region and rank zero.

`rationalUnramifiedCancelledDenominator` chooses this `d` using classical
choice. Its four accompanying lemmas give nonzeroness in the algebra,
divisibility of the original denominator, nonvanishing at every point of
`U`, and the uniform regular-numerator property.

## Provenance and scope

The construction is derived from the displayed local hypersurface
divisibility premise, the published actual regular scalar algebra and its
unique factorization, dense nonzero loci, and continuity. It does not invoke
an external representation-theoretic result as a replacement for these steps.
The paired statements describe the implemented proof.

This scalar result does not prove the assumed local hypersurface theorem.
It also does not construct a regular vector or operator numerator, establish
continuity or convergence of an actual standard integral, prove generic
rationality, or prove the host conditional standard intertwining theorem.
