# Bounded-continuous smoothing and finite-factorization criteria

`HilbertSchmidtBoundedContinuousLiftStatement` is a conditional criterion for
an actual bounded endomorphism A of a complete complex Hilbert space E.
The hypotheses supply a topological measurable space X with its Borel
sigma algebra, a finite measure μ, a complex linear isometry
j : E → L²(X,μ), and a bounded complex-linear map
S : E → (X →ᵇ ℂ). For every z the L² class of S(z) must equal j(A(z)).
The conclusion is the existing predicate `IsHilbertSchmidt A`.
The isometry need not be surjective. In particular this formulation is
suited to the inclusion of a closed Hilbert subspace of L². It neither
chooses a representative for every L² class nor asserts injectivity of
Mathlib's bounded-continuous-to-L² map.

`TraceClassFiniteFactorizationSmoothingStatement` takes the same E, X, μ
and j and an actual nonunital complex-linear, additive and multiplicative
map R from a supplied nonunital ring T to the bounded endomorphisms of E.
The module structure and the `IsScalarTower` and `SMulCommClass` instances
make multiplication in T compatible with complex scalar multiplication on
both sides. No unit, topology or algebra-existence theorem for T is asserted. There are two
additional hypotheses. For **every** f in T there must exist a bounded
linear lift S as above for R(f), with its own bound. Also every f must be
a finite sum of products aᵢbᵢ in T, indexed by Fin n for some n depending
on f. Then every R(f) is trace class. No common choice, uniform bound over
f, or continuity of the assignment f ↦ S is required. Scalar coefficients
in a finite linear combination can be absorbed into one factor because
the scalar action is compatible with multiplication; the stated
hypothesis itself is the explicit finite-sum identity. Operator
multiplication is composition in the order R(a b)=R(a)∘R(b).

`BoundedContinuousSmoothingCriteriaStatement` is the conjunction of these
two criteria. E, X and T have independent universe parameters u, v and w.
Neither proposition assumes a Hilbert–Schmidt or trace-class conclusion.
The single-operator lift conclusion is only Hilbert–Schmidt; the
trace-class conclusion uses lifts for all factors together with
multiplicativity and finite product factorization.

These are internal analytic adapters motivated by Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Lemma 9.3.3,
printed pp.247–248, one-based PDF pp.259–260, registered source
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The source derives the Hilbert–Schmidt step from bounded evaluations and
finite quotient volume and then uses finite convolution factorization
for the trace-class step. Theorem 4.2.9, printed p.110, one-based PDF
p.125, states that each compactly supported smooth function on the local
Lie group is a finite sum of convolutions of such functions. The adelic
extension used in Lemma 9.3.3 is assigned there to Exercise 9.8; it is not
provided by this criterion. The complete five-page author errata
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no correction to either cited numbered result.

The supplied isometric realization, actual bounded-continuous lifts,
nonunital representation and finite product factorizations are internal
explicit hypotheses. Proving the automorphic finite-volume theorem,
constructing the closed invariant cuspidal space, its smoothing lifts and
their all-test-function estimates, and proving adelic convolution
factorization remain separate obligations. These targets contain no
adelic group or automorphic space and establish no cuspidal discreteness,
finite multiplicity or spectral decomposition.
