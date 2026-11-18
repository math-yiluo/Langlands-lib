# Unitarity from square-integrable coefficients on the supplied central quotient

`Langlands.HarishChandraSchwartz.LeftHaarQuotientDualForm.positiveForm`
constructs an invariant positive definite Hermitian form on the smooth dual
from a vector whose orbit spans the representation. It integrates the
coefficient pair of `LeftHaarDualForm.integrand` on the supplied central
quotient, with the arguments exchanged to match Lean's inner product convention.
It uses a unitary central character, smoothness, left Haar measure and the
`MemLp` hypotheses for all smooth-dual coefficient norms.

Complex polarization expresses the integrand as a linear combination of four
squared coefficient norms. The `MemLp` hypotheses give integrability of those
squares in the supplied measurable space. Smoothness gives continuity of the
integrand in the quotient topology. Left multiplication preserves the Haar
measure. When the translation is almost everywhere measurable, invariance of
the integral follows by change of variables. In the other case, Mathlib's
formula for the total measure map makes the measure a Dirac measure. An almost
everywhere measurable integrand is then almost everywhere constant, and open
positivity makes a continuous integrand constant everywhere. This also gives
invariance of the integral in that case.

A nonzero smooth functional is nonzero on some vector of the spanning orbit.
The diagonal integrand is then positive on a nonempty open set, so its integral
is positive. The theorem
`Langlands.HarishChandraSchwartz.isUnitarizable_of_irreducible_quotient_memLp`
chooses a spanning orbit by irreducibility. The published admissible duality
lemmas give an invariant positive form on the smooth bidual and an injective
bidual map, along which the form pulls back. Compact open cofinality is supplied
to these lemmas.

This is an internal extension of the Library's `LeftHaarSquareIntegrableUnitarity`
construction. It supplies the unitarity step for `DenseUnitaryIrreducibilityStatement`,
whose measurable quotient is an explicit input.
