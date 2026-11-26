# The pair epsilon identity at the canonical character

`witnessed_pairEpsilon_canonical` uses `witnessed_isPairFactorMatch` for two witnessed generators at the finite component of the standard global additive character. Its epsilon comparison is an instance of Henniart's Corollary 2.3 at the canonical self-dual measure for every supplied system.

`witnessed_isUnitaryPairEpsilonFactor_weil` transports the arithmetic certificate to the two virtual Weil classes. On the automorphic side, `exists_equiv_unitarizableSupercuspidalProduct` and the equivalences in the automorphic certificate transport the two local components to their full unitary inductions. `isUnitaryPairEpsilonFactor_of_isLanglandsPairEpsilonFactor` then gives the virtual JPSS certificate of the same monomial. `relativePairEpsilonFactor_of_witnessed` extends the result to the graph of the isometry.

`relativePairEpsilon_canonical` supplies the canonical-character epsilon comparison for `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement` from Henniart's Corollary 2.3.
