# Actual refined-chart and scalar-test comparison squares

This module connects actual comparisons between original test charts
with their actual refined chart maps and supplied coefficient-chart maps.
All square edges retain their given actual inverse formal maps.

`CoverRefinement.parentOrderTestIso` follows the actual transition from a
specified original chart to the selected parent, then the inverse actual
finer-chart identification. Its complete series is the original transition.
`Comparison.testIso_refinement` composes these two corrections with the given
test comparison. The actual target transition cocycle and self-transition
identity cancel the reverse target transition. Complete formal-map
extensionality and inverse uniqueness prove the integral square.
`refinementTestSquare` packages its four rationalized integral maps.

`originalTestIsoOnRestrictedTest` evaluates the actual original comparison
between the retained outer original charts on the restricted test, then
transports the integral isomorphism using the proved equality of test scalar
structures. `testIso_baseChangeAlong_square` applies the proved supplied-target
conjugation equation and composes with the target coefficient chart map.
The generic integral `Iso.conjugate_square` uses the actual target inverse
law to cancel that correction. `baseChangeAlongTestSquare` packages the four
specified rationalized maps and their equation.

Generic rings and rational fields have separate universes and arbitrary
finite source and target coordinate types; rationalization uses the existing
domain/fraction-field assumptions. The special-atlas operations retain their
local-field, central-division and embedded-field hypotheses. Every specified
chart has actual test-unit evidence. Covers may be infinite and coefficient
maps may merge generators. No framed comparison base change or representing
object is asserted here.
