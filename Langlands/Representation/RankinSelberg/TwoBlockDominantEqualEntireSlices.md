# Entire equal-rank determinant-slice coefficients

This internal deduction treats a fixed actual coefficient of any smooth test
representation, a fixed row Schwartz–Bruhat function and a pointwise entire
family of inverse Whittaker functions of the same rank. The family has one open
right level. Every literal equal-rank determinant-slice integral is integrable,
and its scalar coefficient is entire. The supplied quotient measure only needs
to be finite on compact sets. Zero coefficients and actual rank one are allowed.

The published `whittakerRowSliceCompactSupport` theorem bounds all supports on
a fixed determinant slice using the fixed test coefficient and row function.
Intersect this compact set with the closed slice. The smooth test vector, common
family level, row-test stabilizer and integral subgroup give one compact open
subgroup that fixes every integrand and preserves the determinant slice.
`exists_finset_rightTranslateOrbit_cover` supplies finitely many disjoint orbits
covering the compact support. The published orbit integral formula expresses
every slice integral as the same finite sum of orbit masses times point values.
The masses and points are independent of the complex parameter, so pointwise
analyticity makes every coefficient entire.

`EqualRankEntireSliceData` packages the actual slice integrability and entire
coefficient conclusions; `equalRankEntireSliceData` proves it under the stated
smoothness, common-level and pointwise-entire assumptions. This supplies no
full-integral convergence or rational continuation. It is an internal composition
of imported compact-support, row smoothness and finite-orbit proofs, with no new
literature assertion or final dominant-rank factor theorem.
