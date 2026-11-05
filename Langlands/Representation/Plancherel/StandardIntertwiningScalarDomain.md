# Scalar convergence and the actual standard-integral domain

This internal construction uses the published actual standard integrand on
`(U ∩ U') \ U'`. Its `scalarDomain` is the submodule of source Levi-normalized
smooth induced functions for which every smooth scalar test is integrable at
every evaluation point. The original ambient right action preserves this
submodule. The existing weak-integral domain is always contained in it.

The remaining results assume a second closed target radical with the same Levi,
regular two-sided Haar measures on the target radical and its actual
intersection with the source radical, and a compatible quotient measure. The
scalar Levi transformation law has exactly the source positive half-character
times the actual quotient-conjugation modulus. It follows directly from
`integrand_levi_mul` and the published scalar change of variables, and requires
neither a representing vector nor scalar integrability.

Under the existing `SquaredModulusCompatibility` hypothesis this factor equals
the target positive half-character. Fix an input function and an evaluation
point `g`, and choose an open right stabilizer `K` of the input. In the Levi
intersect the inverse image of `K` under `m ↦ g⁻¹ m g` with the open kernel of
the target half-character. Scalar Levi covariance at the inverse of an element
of this subgroup, together with right invariance of the input, proves invariance
of the scalar-integral functional under the smooth contragredient.

If the Levi is closed and the inducing representation is admissible, compact
open subgroups of the Levi are cofinal. The integral functional therefore lies
in the smooth bidual and the scalar-integral representability construction,
using admissible bidual surjectivity, produces a representing vector in the
original carrier. Applying this at every evaluation point proves
`scalarDomain_eq_domain`.

The construction is derived from the current actual-function and smooth-duality
interfaces. It assumes and does not prove squared-modulus compatibility. It
supplies no scalar convergence estimate, rational continuation, or denominator
regularity theorem. In particular it is a reduction of the representability
obligation, not a proof of the full conditional intertwining statement. The
ambient group and representation carrier have independent universes.
