# Separation by the infinite compact evaluations

`tensorMap_family_injective` assembles jointly injective families of linear maps on a finite collection of vector spaces. Each family is tested by scalar linear functionals on its outputs. Those functionals separate each output space, and the Library's injectivity of indexed scalar evaluation then separates the tensors. Reindexing by `Fin` lets the proof use the same scalar evaluation theorem for any finite index type.

`infiniteEvaluationFamily` is the linear map to the functions on the actual infinite compact group that takes a tensor to all its compact evaluations. `infiniteEvaluation_injective` applies this result to the real and complex block evaluations of the original-order standard modules. The compact group in units at each place is reached by the matrix-unitary group. The actual infinite compact in turn realizes every simultaneous tuple of unitary matrices by `infiniteCompactCoordinates`.

This is an internal separation argument for the scalar inducing model of `CuspidalIsobaricAutomorphyStatement`. Flath (1979), §2, pp. 180–181 (PDF 176–177), gives the tensor product context. The proof uses the Library's scalar indexed tensor evaluation and the actual compact coordinate equivalence.
