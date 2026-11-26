# Pair L-factors on the generated span

The JPSS pair L-polynomial exists and is unique for each pair of unitary supercuspidal basis classes at a nontrivial character and self-dual measure. Existence uses `Whittaker.SupercuspidalKirillovProof.exists_functional`, `RankinSelberg.isOfWhittakerType_of_isGeneric` and `RankinSelberg.symmetricLPolynomialExists` on representatives. Uniqueness and the constant coefficient come from `IsPadicSymmetricLPolynomial.unique` and `IsPadicSymmetricLPolynomial.coeff_zero`.

`PadicSupercuspidal.unitaryPairLHom` extends the inverse L-polynomial units by integer bilinearity. `isUnitaryPairLFactor_iff` identifies its value with the virtual product over the two supports. On the Weil side, `LocalWeil.unitaryPairLFactor_eq_of_expansion` evaluates the factor of two witnessed generators on their full local representations.

`pairedLattice_bilinear_eq` applies span induction in both variables. `relative_bilinear_graph` then uses `relative_graph_mem_pair` to restrict the identity to the graph of the generated isometry. For L-factors the two maps are `unitaryPairLHom` and the exact-group L-factor composed with `LocalWeil.unitaryRealize`. Their agreement on generator pairs gives `relativePairLFactor_of_witnessed`, the span step for `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
