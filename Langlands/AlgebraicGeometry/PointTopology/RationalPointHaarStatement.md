# Regularity of Haar measures on actual rational points

Author: Worker 1650.

`RationalPointHaarRegularityStatement` is an internal adapter for the actual
identity-test rational points of an affine group scheme locally of finite
type over any nonarchimedean local field, with the existing rational-point
topology and its Borel sigma algebra. The field universe is arbitrary.

It asserts that this point space is second countable and that every supplied
left Haar measure is both regular and inner regular with respect to compact
sets. It makes no smoothness, connectedness, reductivity, characteristic,
splitting, normalization or right-invariance assumption.

This derived statement assembles the published finite-coordinate
second-countability theorem and rational-point comparison with Mathlib's
regularity results. It does not assert nullness of algebraic subsets or of an
open-cell complement; those require separate arguments.
