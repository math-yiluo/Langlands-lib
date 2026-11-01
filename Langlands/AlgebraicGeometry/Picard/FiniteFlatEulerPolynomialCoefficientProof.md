# Native finite-flat rank in actual Euler differences

This proof establishes
`FiniteFlatEulerPolynomialCoefficientStatement`, an independent coefficient
comparison needed for the leading-coefficient target.

`coherentEulerSequence_finiteFree` compares the actual coherent Euler sequence
with the rank multiple of the Euler characteristics of the actual line-bundle
tensor powers. Symmetry of the explicit sheaf tensor puts the line bundle on
the left, so the finite-free Euler theorem applies.
`coherentEulerSequence_finitePushforward` uses the same symmetry and the actual
affine projection comparison to identify the pushforward coefficient sequence
with the Euler values of the pulled-back tensor powers.

`finiteFlat_topEulerDifference_eq_zero` obtains finite affine sections and
quasi-coherence of the actual structure-module pushforward from the finite-flat
structure comparison. Its generic-basis theorem gives a nonempty affine open
where this pushforward is the actual free sheaf on the native rank at the
specified target point. Restriction of the global free sheaf identifies the two
coefficients there. The irreducible closed set is the whole integral target;
its height is at most the given dimension bound, and both sheaves vanish on
its empty complement. The proved dense-open coherent comparison therefore
makes the indicated difference vanish after that many forward differences.
The two sequence identities above put its conclusion in terms of the actual
Euler invariants.

These are internal consequences of the actual sheaf and cohomology
constructions. No numerical rank identity or leading-coefficient certificate
is assumed.

`finiteFlat_eulerPolynomial_coeff` substitutes any rational polynomials that
represent the two actual Euler sequences into the vanishing difference. Newton
reconstruction then compares their coefficients in the dimension bound.

The final theorem introduces exactly the stated actual scheme, morphism,
cohomology and polynomial hypotheses and applies that coefficient comparison.
It does not require ample exact degree or the ample Euler polynomial theorem.
