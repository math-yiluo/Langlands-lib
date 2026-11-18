# The geometric endomorphism trace comparison

The theorem `Langlands.AbelianScheme.geometricEndomorphismTraceComparison`
proves exactly
`Langlands.AbelianScheme.GeometricEndomorphismTraceComparisonStatement.{u}`,
in its full universe scope. Thus, for every actual abelian scheme over an
algebraically closed characteristic-zero field and every prime, the actual
rational Tate module is finite dimensional, has dimension twice each supplied
relative dimension, and the fixed rational geometric endomorphism trace agrees
with the actual prime Tate trace on every rationalized endomorphism.

The proof applies `geometricDegreeTraceReduction` with
`endomorphismDegreeLinePolynomial`, which supplies the common rational degree
function and its polynomial restrictions to endomorphism lines. The theorem
`isogenyDegreeTateDeterminantNormReduction` assembles the actual Tate determinant
norm comparison from four published results.

- `IsogenyKernelCard.finrank_eq_natCard_ker`, identifying native isogeny rank
  with the number of actual geometric kernel points;
- `isogenyKernelCardTateDeterminant`, identifying the prime-adic norm of this
  kernel cardinality with the actual rational Tate determinant norm;
- `tateDeterminantNonzeroSurjective`, making an endomorphism with nonzero
  Tate determinant surjective;
- `SurjectiveIsogeny.isIsogeny_of_surjective`, making such a surjective
  abelian endomorphism an isogeny.

The applied degree-to-trace reduction chooses a rational degree polynomial
before choosing a prime, identifies its scalar extensions with the actual
Tate characteristic polynomials, and takes the negative next coefficient.
Its integral trace extension then proves the full comparison, including
dimension zero and every rationalized endomorphism.
