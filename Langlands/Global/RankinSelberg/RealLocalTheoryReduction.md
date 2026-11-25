# Local analytic and model inputs for the real-place functional equation

This internal reduction separates the remaining higher-rank work into four
named premises:

- `RealLocalUnequalJacquetStatement`: the full analytic equation for unequal
  ranks on the explicit local real coefficient spaces.
- `RealLocalPositiveEqualJacquetStatement`: the same for positive equal rank
  index and every Schwartz function.
- `RealPlaceWhittakerModelStatement`: every actual global restriction with
  the specified real parameter belongs to the corresponding coefficient space,
  for the original and inverse additive characters.
- `RealPlaceContragredientPairLStatement`: the denominator of the pair factor
  of the two actual contragredient parameters equals that of the explicitly
  dualized original blocks.

The main proposition `RealPlaceLocalTheoryReductionStatement.{u}` is the
implication from these four premises to the exact Library statement
`RealPlaceFunctionalEquationStatement.{u}`. None of the four premises is
proved in this module.

The local analytic premises use the already defined `RealJacquet` equation
packages, so they retain integrability, holomorphy, meromorphic continuation,
agreement on a right half-plane and the multiplied-out functional equation.
They retain the negative-parameter source conventions and the positive
self-dual Haar scale. Their local signs are the explicit parameter
determinants at minus one; their dual factors use `RealLocalJacquet.dualBlock`.
The equal-rank premise excludes `r = 0`, which is supplied by the included
Tate and actual global rank-one proofs.

The coefficient space is the internal one defined in
`RealLocalWhittakerModel`. Identifying its smooth moderate-growth algebraic
intertwiners with a continuous induced-model Whittaker space requires a
globalization and continuity argument. Establishing the local analytic
premises therefore includes the necessary comparison and normalization work;
the reduction does not assert that the original analytic theorem applies
directly to the new space.

The implemented proof applies the membership premise to `W` and `W'`,
then applies the corresponding local analytic premise. The proved real
standard-module nonvanishing theorem and the parameter injection identify
each local determinant with the actual compact minus-one scalar, via
`RealLocalJacquet.realMinusOneScalar_eq_parameter`. The dual-factor premise
rewrites the denominator to the actual contragredient parameters. This
supplies `RealPositiveJacquetRestrictionEquationStatement`, and the Library
theorem `realPlacePositiveAnalyticReduction` finishes the implication.

The dual-factor premise requires equality only of the two entire denominator
functions. It does not require a permutation of block lists or assert that
the inverse-block presentation is unique. All original global hypotheses,
both rank cases and the free field universe `u` are retained in the conclusion.

The provenance is internal composition and interface refinement. This is a
conditional intermediate result. The model premise is proved in the Library
as `realPlaceWhittakerModel` (module `RealPlaceWhittakerAnalyticProof`); the
three other premises, and therefore the unconditional full functional
equation, remain open.

The entry proposition and the implemented theorem were checked in the pinned environment with no errors or warnings. The universe `u` is free, and the theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
