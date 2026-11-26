# Pair epsilon factors on the generated span

`VirtualRepresentation.epsilonHom` extends a basis-pair certificate \(c(q^{-s})^m\) by integer bilinearity, with values in \(\operatorname{Additive}(\mathbb C^\times)\times\mathbb Z\). The first coordinate gives the multiplicity-weighted product of the coefficients and the second gives the corresponding sum of the exponents. `virtualEpsilon_iff` uses uniqueness on basis pairs to express the virtual relation as the graph of this map.

For unitary supercuspidal basis classes, `TemperedLFactorGamma.epsilon_exists_of_whittakerType` gives certificates at a self-dual measure and `IsPadicSymmetricEpsilonFactor.unique` gives uniqueness. For unitary Weil classes, `Correspondence.isArithmeticPairEpsilonFactor_pairEpsilonHom` gives certificates and `IsArithmeticPairEpsilonFactor.unique` gives uniqueness. These results identify both virtual relations with their respective bilinear evaluations.

`relativePairEpsilonFactor_of_witnessed` applies `relative_bilinear_graph` to the two evaluations. If they agree on all generator pairs at the given character, measure and system, their common value gives a certificate for every pair on the graph of the generated isometry. This is the span step for the epsilon clause of `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
