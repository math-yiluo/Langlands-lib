# Actual subgroup constant-term descent and convergence

Let `F` be a number field, `G/F` an actual affine group scheme, and
`U : GroupScheme.SubgroupFunctor G`. On the actual quotient
`Q = U(F) \ U(A_F)` constructed in `AdelicSubgroupQuotient`,
`constantTermIntegrand F G U f g` is the function whose value on the class of
`n` is `f(n*g)`. Here `f` belongs to the existing actual
`ContinuousRationalFunctions F G`, with positive right translation.
The supplied measurable structure on `Q` and measure `μ` are explicit
parameters of integration.

Descent uses an actual rational-subgroup image witness, multiplication
associativity, and the original function's rational left invariance.
Continuity follows from continuous subgroup inclusion and multiplication,
then the quotient universal property. For each `g` descent is complex
linear. Translating `f` by `h` replaces `g` by `g*h`.

`HasConvergentConstantTerm μ f` states Bochner integrability of every
integrand. This predicate defines `convergentConstantTermSubrepresentation`
inside the original continuous representation: zero, sums and scalar
multiples use the corresponding integrability laws, and translation uses
the preceding `g*h` identity. `constantTerm` itself is the totalized Bochner
integral. Its additivity is proved with explicit convergence hypotheses.
The resulting `constantTermLinearMap` on
`ConvergentConstantTermFunctions` is complex linear and intertwines positive
right translation with positive translation of output functions.

`constantTerm_smul_measure` records the exact normalization law for every
extended nonnegative scalar `c`: the integral for `c • μ` equals
`c.toReal` times the original integral. This is the totalized integral law,
including `c = ∞`, rather than an assertion of convergence for infinite
rescalings.

These are derived constructions from actual subgroup evaluation,
homogeneous-quotient descent, and the Bochner integral. No literature
theorem is assumed. They apply to an actual subgroup functor, including
unipotent radicals when supplied as such. No arbitrary family of subgroup
functors is asserted to enumerate all rational parabolics. Compactness of
unipotent rational quotients, canonical invariant measures, convergence for
every continuous function, left unipotent invariance of the integral,
smoothness of output functions, general cuspidality, and comparison with
the original matrix constant terms remain separate obligations.
