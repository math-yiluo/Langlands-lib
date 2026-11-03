# Transport of smooth contragredients

For representations `ρ` and `σ` of an arbitrary topological group over a
commutative ring, `Langlands.smoothContragredientEquiv e` sends an equivalence
`e : ρ.Equiv σ` to the reverse equivalence of their smooth contragredients.
Its forward map is precomposition with `e`; precomposition with `e.symm`
gives the inverse.

This is the unchanged generic construction originally published in
`Classification.HighestDerivativeSupportShiftProof` and reused in
`Aubert.General.RationalInductionDualityReduction`. Both namespaces retain
abbreviations for the shared definition. Credit for the construction remains
with the authors of the original classification module. Moving the definition
here adds no classification assumption or new mathematical statement.
