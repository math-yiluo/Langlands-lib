# Weil pair epsilon certificates of exact expansions

`epsilonHom_unitaryBasisPairEpsilon_eq` identifies the bilinear epsilon map on the unitary Weil lattice with `Correspondence.pairEpsilonHom` of the two realizations in continuous exact \(K_0\). On each basis pair the maps give certificates of the same two zero-monodromy classes by `exists_unitaryRealize_generator` and `isArithmeticPairEpsilonFactor_pairEpsilonHom`. `IsArithmeticPairEpsilonFactor.unique` identifies the two values, and bilinearity gives the map identity.

`isUnitaryPairEpsilonFactor_of_expansion` substitutes any two witnessed exact expansions into this identity. `witnessed_isUnitaryPairEpsilonFactor_weil` also applies `WitnessedGenerator.localExactClass_localMap_eq` to put both expansions on the first generator's local map. The result takes a certificate of the two full local Weil representations to the Weil-side virtual certificate needed by `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
