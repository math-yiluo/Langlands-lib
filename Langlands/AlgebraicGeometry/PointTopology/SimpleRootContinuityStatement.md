# Local continuity of a simple root in a monic polynomial family

Author: Worker 208.

`MonicSimpleRootContinuityStatement.{u}` concerns the actual polynomial family

```text
p(c) = X^n + sum (i : Fin n), C(c(i)) * X^i
```

over a complete nontrivially normed field `K`, where `n > 0`. The coefficients
`c : Fin n → K` carry their usual finite product topology. These are precisely
the degree `n` monic polynomials with their lower coefficients as parameters:
the lower sum has degree less than `n`, as in Mathlib's
`Polynomial.degree_sum_fin_lt`.

Given `p(c)(a) = 0` and `p(c).derivative(a) ≠ 0`, the target supplies a function
`ψ` on coefficient vectors with `ψ(c) = a`, continuous at `c`. For all
coefficients sufficiently near `c`, `ψ(C)` is a simple root of `p(C)`.
Moreover, on a neighborhood of `(c,a)` in the product of coefficient and
root spaces, `p(C)(t) = 0` if and only if `ψ(C) = t`. This gives both a
continuous choice of nearby simple root and uniqueness in a sufficiently
small root neighborhood. The function is defined on the entire coefficient
space, but no root or continuity assertion away from the stated
neighborhood is made.

The field has arbitrary characteristic and no local compactness or
archimedean hypothesis. All objects use an arbitrary common universe `u`.
The derivative in the hypotheses and conclusion is the formal polynomial
derivative evaluated in `K`.

## Provenance and corrected uniqueness

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.11, discussion of continuity of simple roots preceding Theorem 4.5.
This statement makes precise the local root argument used there to obtain
openness of smooth maps on points.

The printed assertion asks for uniqueness throughout the prescribed
epsilon-ball for every positive epsilon. That wording requires a
qualification. For `K = ℝ`, `g(u) = u(u-1)`, `a = 0` and `ε = 2`, the
polynomial `G = g` satisfies every positive coefficient bound, but both
`0` and `1` lie within distance `2` of `a`. Both are simple roots, since
`g'(0) = -1` and `g'(1) = 1`. Thus no coefficient bound makes that entire
ball contain a unique root. The present target uses uniqueness on a
sufficiently small neighborhood of `(c,a)`, which is the local conclusion
needed by the source proof. Continuity still places the chosen root within
any prescribed positive distance of `a` after shrinking the coefficient
neighborhood.

This is a derived, corrected statement unit. It supplies no proof by itself
and does not assert the later scheme-theoretic reduction from smooth maps
to polynomial presentations.
