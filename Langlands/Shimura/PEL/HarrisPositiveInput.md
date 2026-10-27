# Positive algebraic PEL input from the Harris signature charts

This internal specialization combines `PEL.PositiveInput` with the proved
theorem `CentralSimpleUnitaryData.positiveRationalSkewTwistExists`.
Its inputs are the actual central simple CM algebra with Harris involution
`D` and its signature charts `C`, together with the number-field and
rational scalar-compatibility instances shown in Lean. There is no external
positive-twist existence-proof argument. The signature charts themselves
remain inputs; their existence is not asserted here.
The alternation, nondegeneracy and group-comparison results additionally
retain the scalar tower from E through K to A used by the trace-form theory.

`harrisPositivePELUnit` selects the rational skew unit beta using that
theorem. `harrisPositivePELAlgebra` constructs the auxiliary algebra with
involution tau(x) = beta sigma(x) beta inverse on the same fields and
algebra. Its real scalar extension is positive, as proved by
`harrisPositivePELAlgebra_isPositive`.

The inverse gamma = beta inverse is skew for tau.
`harrisPositivePELForm` is the normalized rational trace form of tau and
gamma. The module proves that it is alternating and nondegenerate,
identifies its right adjoint with the original rational Harris involution
sigma, and records the resulting right-multiplication adjoint identity.

`harrisPositivePELSimilitudesEquiv` constructs the group equivalence from
the opposite of the original rational Harris similitude group to the
algebra-linear similitude group of this form. Its action is
x maps to x g, and its multiplier agrees with the original multiplier.
The opposite convention accounts for right multiplication.

All these definitions apply the published construction to the published
existence theorem. The accompanying proofs are applications of the
corresponding `positivePEL` lemmas; the action and multiplier formulas
hold by definition. This is derived internal content, with mathematical
provenance in those two imported modules and their source discussions.

The positivity proved here is positivity of the auxiliary algebra
involution. Hodge polarization positivity and its sign, scalar-extension
comparisons for the form and group, finite-place conditions, integral
lattices, adelic comparisons, and moduli representability remain separate
obligations. No output scheme or local system is supplied as an input,
and this module constructs neither.
