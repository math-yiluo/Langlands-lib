# The integral subgroup in Cartan coordinates

Author: Worker 246.

`Langlands.ProductLeviTempered.discreteValuation_integer` identifies the integer
ring of the specified discrete valuation with `T.Integers`.
`Langlands.ProductLeviTempered.maximalCompact_eq` consequently identifies
`CartanQuotient.maximalCompact T N` with the range of integral invertible matrices
for the supplied valuation, in every rank.

Both declarations and proof bodies are moved unchanged from
`Langlands.Representation.Classification.ProductLeviTemperedSufficiencyProof`.
Their historical namespace is retained. This lower module lets strict Cartan
coefficient bounds and product-Levi sufficiency reuse the same comparisons
without importing one another's analytic conclusions.
