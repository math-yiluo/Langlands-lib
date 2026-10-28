# Polynomial annihilation on a finite joint differential orbit

`Langlands.Global.ArchimedeanGL.JointOrbitPolynomialAnnihilationStatement K n`
retains the published actual smooth functions, joint differential orbit
span, enveloping center and compact-generated enveloping subalgebra, for
an arbitrary number field `K : Type u` and every natural rank `n`.

For each smooth function `f` with `IsJointFinite K n f`, each central
element `z` and each element `b` of the actual compact enveloping
subalgebra, the proposition asks for a complex monic polynomial `p` with
degree equal to the dimension of `jointOrbitSpan K n f`, such that

```text
D(p(centerInclusion z + b.val)) g = 0
```

for every `g` in that whole joint orbit span. Polynomial evaluation occurs
in the original enveloping algebra, and `D` is the published genuine
`envelopingAction`. The same `p` annihilates every vector in this orbit
span; it may depend on `f`, `z` and `b`. A scalar multiple of a compact
operator is included by choosing that multiple as `b`. No bound uniform
over all functions or operators is asserted.

This is an internal linear algebra prerequisite, with no external
literature attribution. The existing joint subrepresentation is invariant
under each center and compact differential operator, hence under their
sum. A prospective proof restricts that sum to the finite-dimensional
joint orbit, takes its characteristic polynomial, applies
Cayley–Hamilton, and transports the polynomial identity through the
subspace inclusion and the actual enveloping algebra action. For the zero
orbit, the monic polynomial of degree zero is permitted. No
positive-rank or nonzero-function hypothesis is imposed.

This module defines the proposition only. It constructs no Casimir
operator or differential symbol and proves no ellipticity, analytic
regularity, jet uniqueness, admissibility, orbit density or reproduction.
In particular, polynomial annihilation alone is not asserted to imply
analyticity. The final automorphic differential-growth theorem remains a
separate obligation.
