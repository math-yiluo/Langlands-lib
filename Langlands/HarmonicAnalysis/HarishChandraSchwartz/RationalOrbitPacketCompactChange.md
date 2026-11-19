# Compact probability normalization of actual rational orbit packets

For a fixed actual standard parabolic and two compact open Iwasawa factors,
`exists_pos_rationalInducedOrbitCoefficientMap_eq_mul_of_compact` compares the
original orbit coefficient maps at the same actual section. The first
coefficient is a fixed positive scalar times the second, uniformly over
the section, unitary orbit parameter, and group point.

The proof specializes `CompactInduction.exists_pos_coefficientMap_eq_mul_of_compact`
using the published standard-parabolic modulus and reductive unimodularity.
Every orbit class has an actual representative, and the formulas for
`rationalInducedOrbitCoefficientMap` at that representative compare the
same vector in the actual induced representation. The scalar passes
through the original weighted Bochner integral by `integral_const_mul`.
This yields `exists_pos_rationalInducedOrbitWavePacket_eq_mul_of_compact`,
with the same character measure and orbit weight on both sides.
