# Arithmetic pair epsilon factors on continuous exact classes

`Langlands.Correspondence.pairEpsilonHom` is an integer-bilinear map on the continuous exact \(K_0\) of local Weil representations. Its values in \(\operatorname{Additive}(\mathbb C^\times)\times\mathbb Z\) encode the coefficient and exponent in \(c(q^{-s})^m\) for a fixed nontrivial additive character and a supplied local-constant system.

`LocalFactor.SpectralConductor.monomialCoefficient` takes the original epsilon value and the integer exponent supplied by `mem_monomialSubgroup`. The former is additive in the additive notation for units by the system's `AdditiveRelation`. The latter is additive by uniqueness of the exponent, using `unitMonomial_eq_of_infinite` on real spectral points.

The bilinear map composes `continuousTensor` with `continuousRestrict` to the bottom Weil subgroup, `continuousTransport` to the carrier universe of the system and `monomialCoefficient` at the transported character and self-dual measure. On two representations it evaluates the tensor of the transported restrictions, by `continuousTensor_ofRepresentation`, `restrict_ofRepresentation` and `tensorEquivOfEquiv`.

`isArithmeticPairEpsilonFactor_pairEpsilonHom` uses `isArithmeticPairEpsilonFactor_of_monomial` to certify this coefficient and exponent for the zero-monodromy pair classes of the two continuous representations. The construction gives the Weil-side bilinearity used in `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
