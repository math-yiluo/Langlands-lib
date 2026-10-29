# The smooth-family comparison from its four geometric inputs

This module assembles the two directions of the field smooth-family
comparison and its lifts. It does not prove the comparison
unconditionally. Both theorems take four Library statements as explicit
hypotheses:

- `cube : Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialitySmoothThirdStatement.{u}`,
  the theorem of the cube over a field with a smooth, geometrically
  connected, not necessarily proper third factor;
- `integrality : SmoothGeometricIntegrality.{u}`;
- `ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}`;
- `lifting : AlgClosedFieldTranslationDifferenceLiftingStatement.{u}`,
  Proposition (7.21) of Edixhoven, van der Geer and Moonen.

## Declarations

In namespace `Langlands.AbelianScheme`:

- `smoothFamilyTranslationInvariance_of_inputs cube integrality ample lifting`:
  proves `SmoothFamilyTranslationInvarianceStatement.{u}`. For an
  algebraically closed field `K`, an abelian scheme `A` over `Spec K` and
  `L : LineBundle A.X.left`, the forward implication is
  `isTranslationInvariant_of_isAlgebraicallyTrivialViaSmoothFamily cube A L`
  (module `TranslationInvarianceOfSmoothFamily`). The reverse implication
  is `isAlgebraicallyTrivialViaSmoothFamily_of_isTranslationInvariant
  integrality ample lifting A L` (module
  `SmoothFamilyOfTranslationInvariance`).
- `smoothFamilyPicardZeroComparison_of_inputs cube integrality ample lifting`:
  proves `SmoothFamilyPicardZeroComparisonStatement.{u}` by applying
  `smoothFamilyPicardZeroComparison_of_field` (module
  `SmoothFamilyPicardZeroComparisonLifts`) to the field comparison above.

## Proof

Both theorems are direct term-mode assemblies of the cited theorems. No
further argument is needed.

## Scope

The hypotheses are the four Library statements, unchanged. With proofs
of all four, the second theorem proves the target statement
`SmoothFamilyPicardZeroComparisonStatement.{u}`.
