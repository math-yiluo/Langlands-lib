# Unequal-rank pointwise factorization from slice comparisons and place tests

`unequalInfiniteWhittakerSliceReduction` proves `UnequalInfiniteWhittakerSliceReductionStatement.{u,uQ}`: the single-presentation `InfiniteWhittakerSliceModelStatement`, `RealUnequalPlaceTestsStatement`, and `ComplexUnequalPlaceTestsStatement` together imply the exact `UnequalPointwiseFactorizationStatement`. Both universe parameters remain free. The three inputs are retained as hypotheses, not proved here.

## Implemented proof

1. For one presentation, `InfiniteWhittakerSlice.exists_normalized_product_of_restrictions` matches each prescribed actual place restriction to a model vector using the supplied `ModelData`. Form the pure tensor of those vectors. The published normalized residual product formula gives one nonzero scalar, independent of the point, times the product over the sum of the real- and complex-place index types. Splitting that product and substituting the chosen model vectors gives the product of the prescribed restrictions on all arguments. This single-rank step adapts the private comparison in `EqualInfiniteWhittakerSliceReduction`.
2. At a fixed field, `unequalInfiniteWhittakerTest_of_placeData` chooses one pair of tests and one quotient measure at each actual infinite place. Apply the single-presentation step to each rank, using the inverse unitary character and its canonical inverse finite components for the smaller rank. This produces two separate product formulas and their nonzero scalars. For each of the ordinary and dual products, finite-product holomorphic nonvanishing gives a nonzero value arbitrarily far to the right. The same chosen restrictions and measures serve both products; the two product nonvanishing witnesses need not use the same spectral parameter.
3. For the universally quantified `UnequalInfiniteWhittakerTestStatement`, obtain the two comparisons from the single-presentation premise and the test witnesses from the local premises. Use the fixed-field assembly and apply `unequalPointwiseOfInfiniteTests` to reach the exact target.

## Scope and provenance

This is an internal composition for the pointwise step of Cogdell 2004, proof of Theorem 4.1, printed p. 219, based on the Library's normalized residual product. It proves no archimedean comparison or local analytic test existence. The fixed-field assembly applies when there are no real places: its real family is then vacuous and its real integral products are one. This observation applies to the assembly lemma, not to an unconditional totally complex pointwise factorization theorem.
