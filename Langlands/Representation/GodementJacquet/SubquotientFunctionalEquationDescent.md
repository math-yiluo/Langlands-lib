# Normalized matrix equation data on actual p-adic subquotients

This module specializes `normalizedMatrixFunctionalEquationDescent` to canonical
p-adic normalizations and removes its two unit-membership premises for nonzero
smooth targets. It retains the field and the two representation carriers in
independent universes, and every actual rank `n + 1`, including rank one.

`Padic.normalizedMatrixFunctionalEquationData_of_coefficient_inclusion` assumes
full normalized data for an ambient representation and inclusion of the actual
bi-smooth coefficient space of a nonzero smooth target. The theorem
`matrixUnitValue` gives actual rational value `1` on both target sides.
`mem_zetaSpan` places these values in their Laurent spans. The general descent
theorem then constructs new normalized polynomials, a complex unit and an integer
exponent for the target. The canonical residue cardinality satisfies `1 < q`.
The supplied scalar additive Haar measure and its self-duality remain unchanged.
The canonical topology and measure instances have explicit names specific to
this module so that it can be imported together with other p-adic analytic
modules without generated instance-name collisions.

`Padic.normalizedMatrixFunctionalEquationData_of_subquotient` assumes a smooth
ambient representation, an actual subrepresentation `A`, and a surjective
intertwiner from `A` to a nonzero target. Smoothness restricts to `A` through its
injective inclusion and descends through that surjection to the target.
The published `Padic.subquotientCoefficientInclusion` supplies exactly the
coefficient inclusion required by the first theorem. Thus the wrapper adds no
target smoothness or unit-membership premise.

Both conclusions are the complete unchanged
`Padic.NormalizedMatrixFunctionalEquationData`, with the same canonical group
measure and absolute value and the same supplied character and Fourier measure.
The polynomials, unit and exponent are allowed to change. All convergence,
continuation, normalized-generator, Fourier-witness and guarded-equation clauses
are retained through the general descent theorem.

These are internal compositions of the named Library results, not new literature
translations. They are relative results with full ambient data as a premise and
do not prove the host unconditional irreducible existence theorem. Worker 364
implemented the wrappers using Worker 704's unit-value construction and descent
route.
