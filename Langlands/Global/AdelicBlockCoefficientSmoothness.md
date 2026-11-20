# Smooth mixed matrix evaluation of the realized Levi coefficients

Fix a tuple of finite adelic Levi blocks. For each realized vector in a block, take the actual smooth infinite slice at that finite argument and apply the mixed matrix coordinate extension. On a pure tensor, `coefficientExtension` multiplies these evaluations at the diagonal blocks of the ambient matrix. The indexed tensor evaluation then gives a linear map on the span of the scalar block coefficients via `coefficientEquiv`.

`coefficientExtension_apply_parabolic` proves the evaluation formula on an actual infinite parabolic matrix. Applying the extension is the same as evaluating the original coefficient at the diagonal blocks paired with the prescribed finite tuple. The proof compares the two evaluation maps on pure tensors using the formula for `finiteSmoothSlice`.

`coefficientExtension_contDiffAt` proves real smoothness at each infinite parabolic matrix. Each diagonal block there is invertible. Its ambient projection is continuous linear, so the extended smooth slice on that block is smooth at the matrix. Finite products, complex scalar multiples and sums give the claim for the whole tensor space.

This internal construction uses the actual smooth slices of the published operator realization and the scalar coefficient evaluation. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), describe the adelic induced sections in which these coefficients occur.
