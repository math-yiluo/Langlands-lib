# Pair L-factors of witnessed generators

`witnessed_isPairFactorMatch` applies `AssociatedTemperedFactorStatement` to two witnessed generators and the finite component of the standard global additive character. `PadicSupercuspidal.exists_equiv_unitarizableSupercuspidalProduct` realizes each witnessed support by normalized induction. `Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct` gives temperedness, and `RelativeWeilGroup.localComponent_isUnitary` gives local Weil unitarity. The comparison uses the first generator's local map for both Weil representations.

`WitnessedGenerator.exists_conj_localMap` and `RelativeWeilGroup.localComponentConjEquiv` identify the zero-monodromy pair classes obtained using the two maps. `witnessed_unitaryPairLFactor` therefore gives the Weil-side factor of the two full local representations. On the automorphic side, `RankinSelberg.IsLanglandsPairLPolynomial.symmetric_of_tempered` gives the JPSS polynomial, and `PadicSupercuspidal.isUnitaryPairLFactor_of_equiv_productInduced` computes its factor in the witnessed supports. `IsUnitaryPairLFactor.change` allows any nontrivial additive character and self-dual measure.

The resulting `witnessed_isUnitaryPairLFactor` supplies the generator comparison in `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement` given Henniart's Corollary 2.3, printed p. 445.
