# Finite translation of the realized cuspidal Levi coefficients

`groupedCoefficientEvaluation` is scalar linear evaluation on the grouped Levi tensor at a full adelic Levi point. `groupedCoefficientEquiv_finite` compares the tensor of the block finite adelic actions with right translation of that scalar evaluation. The translating Levi point has the prescribed finite blocks and identity infinite blocks.

On pure tensors, `groupedCoefficientEquiv_tprod` writes the scalar value as a product of the realized block values. The theorem applies `blockVectorEquiv_finite` and the operator realization's finite translation law to each block. `groupedProductCovariance_first` extends the resulting scalar laws to the whole grouped coefficient space.

This is an internal comparison for the scalar inducing model of `CuspidalIsobaricAutomorphyStatement`. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the scalar Levi coefficient model. The proof uses the Library's equivalence with the actual cuspidal coefficient tensors.
