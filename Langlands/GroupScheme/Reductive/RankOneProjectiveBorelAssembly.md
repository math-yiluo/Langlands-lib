# The rank-one projective Borel route from its remaining structural inputs

Worker 1547 composes the actual prescribed-Borel quotient construction,
Worker 1549's rooted proper-Borel and normalizer constructions, and the
projective fixed-point and regular quotient-curve consumers. This is an
internal conditional reduction, not an unconditional proof of
`RankOnePositiveRootUniquenessStatement`.

All fields have arbitrary characteristic and live in universe `u`.

`prescribedBorelProjectiveCurveData` constructs actual proper quotient data
for a prescribed Borel and pairs it with a proof that its dimension is at
most one. Its two structural premises are the solvable proper fixed-point
statement and the projective torus fixed-point dimension statement. It also
retains the split maximal torus, pairwise root dependence, actual torus
factorization, conjugacy of maximal tori inside this Borel and all-test
whole-torus centralizer containment. It requires no root or proper-subgroup
premise. The returned data contain the quotient scheme, projection,
properness, smoothness, surjectivity, quasi-compactness and exact all-test
fiber law; the dimension proof concerns this same quotient.

`positive_roots_eq_of_prescribedBorel_of_projectiveFixedPoints` works over
an algebraically closed field. The ambient group is connected reductive,
the given torus is split and maximal, and every pair of its actual adjoint
roots is integrally dependent. A prescribed Borel inclusion `b : B → G`
is assumed to be a proper subgroup (`¬ IsIso b`), and the original torus
map factors through it by the supplied `t` and factorization equality.
The remaining subgroup hypotheses are conjugacy of maximal tori inside
this same `B`, and containment of the whole-torus centralizer in the range
of `b` on every relative scheme test.

The two theorem premises are `SolvableProperFixedPointStatement` and
`ProjectiveTorusFixedPointDimensionStatement`. The former constructs an
actual proper quotient of this precise Borel using
`properQuotientData_of_solvableProperFixedPoint`. Its projection is smooth,
surjective and quasi-compact and has the exact right-coset fiber criterion
on every test, including nonaffine and nonreduced tests. The latter applies
to the quotient's constructed equivariant projective embedding. Together
with internal torus conjugacy and rational centralizer containment, obtained
by restricting the given all-test containment, the fixed-point sign
embedding forces actual quotient dimension at most one.
This construction is packaged by `prescribedBorelProjectiveCurveData`,
which the root-uniqueness theorem consumes.

When two roots are positive on the original cocharacter, the first root
provides an actual relative root. Thus
`nonidentityNormalizerOfRootedSolvableQuotient` constructs a rational
normalizer point with nonidentity class in the relative Weyl quotient.
No such class or moving quotient section is an additional premise.
The regular quotient-curve theorem then proves the roots equal. Its
regular refinement preserves positivity on the original, possibly
nonregular cocharacter. The theorem assumes no normal-solvable-torus
statement, divides by no integer and restricts no characteristic.

`rankOneAlgClosedPositiveRootUniqueness_of_projectiveBorelInputs` retains
those two fixed-point premises and assumes the existing
`SolvableMaximalTorusConjugacyStatement` and
`AlgClosedMaximalTorusCentralizerStatement`. Given the first root in the
uniqueness assertion, it constructs a proper Borel through the specified
torus with `exists_proper_isBorelPair_of_relativeRoot`. Closedness gives
affineness of the Borel; the conjugacy premise applies to its smooth,
connected, solvable group scheme. Self-centralization identifies the
whole-torus centralizer with the torus range, which the actual
factorization places inside the Borel range on every test. The preceding
prescribed-Borel theorem now proves the exact algebraically closed
uniqueness assertion. The rootless case is handled by the universal
root-membership hypotheses, so no root-existence premise is added.

`rankOnePositiveRootUniqueness_of_projectiveBorelInputs` additionally
assumes `MaximalTorusBaseChangeForwardStatement` and applies the published
algebraically closed reduction. This preserves every field, split maximal
torus and cocharacter in the unchanged
`RankOnePositiveRootUniquenessStatement`, including finite and imperfect
fields. The actual roots, their integral dependence and their pairings
are transported by the published base-change results.

The provenance is composition of the named internal Lean constructions.
The implementation supplies the Borel, proper exact quotient, projective
embedding, dimension bound and nonidentity normalizer class from the five
displayed structural premises. Those five premises remain proof
obligations. This module neither asserts them unconditionally nor proves
the final all-field target without them. It does not use the excluded
regular-cocharacter Borel, dynamic parabolic or rank-one solvable/Borel
classification statements.
