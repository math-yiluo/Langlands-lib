# Parameter differentiation of genuine derivative orbits

Author: Worker 94. This is an internal derived helper for the
smooth scalar orbit coefficient proof.

The enveloping induction lemma uses complex tensor induction to pass from
real to complex generators. Tensor-algebra induction is applied to the
stronger property that left multiplication preserves the desired predicate,
and then descends through the defining quotient. Only the unit, addition,
complex scaling and left real generator multiplication are required.

The actual two-variable derivative orbit is smooth on the product of the
open matrix units domains. Its evaluation derivative is exactly left
multiplication by a real enveloping generator. At enveloping index one,
the parameter derivative follows from the chain rule for matrix
multiplication and has the direction `g*X`, with the published positive
right translation convention. The evaluation point multiplies on the left
of the translating parameter. These are internal consequences of the
published actual differential action.

The general parameter derivative identity uses the left generator induction.
At a generator step the evaluation partial derivative expresses left
multiplication in the enveloping index. The two partial derivatives commute
by symmetry of the second Fréchet derivative. The induction hypothesis holds
at every evaluation point in the open units set, so its two sides have equal
evaluation derivatives. This closes the step without assuming a calculus on
the derivative-topology vector space.
