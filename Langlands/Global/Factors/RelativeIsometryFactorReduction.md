# Relative isometry factors from the tempered pair comparison

`Langlands.Global.PoleComparison.RelativeIsometryFactorReductionStatement.{uF,uW,uP,uE}` states that `AssociatedTemperedFactorStatement.{uF,uW,uP,uP,uE}` implies `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement.{uF,uW,uP,uE}`. The two presentation universes in the tempered comparison are both `uP`, the presentation universe carried by the witnesses. `relativeIsometryFactorStatement_of_tempered` proves the implication.

`relativeIsometryDeterminantCompatibility` proves the determinant clause for every geometric reciprocity candidate. `Correspondence.isSelfDual_localSelfDualHaar` supplies a self-dual measure for each nontrivial additive character.

The witnessed unitary supercuspidal supports give tempered local components by `exists_equiv_unitarizableSupercuspidalProduct` and `isTempered_of_equiv_unitarizableSupercuspidalProduct`. Along the first generator's local map, both Weil restrictions are unitary. This gives the local hypotheses of Corollary 2.3. Conjugacy of the witnessed maps allows the comparison to use this common restriction. `witnessed_isUnitaryPairLFactor` computes the L-factor on the two supports and makes it independent of the character and self-dual measure. `relativePairLFactor_of_witnessed` extends the identities by bilinearity to the graph of the isometry.

`relativePairEpsilon_canonical` gives a common virtual certificate at the canonical additive character for the supplied system. `relativePairEpsilonScaling` uses the determinant and degree identities to transport that certificate to the requested character and measure. The pole-comparison premise is stronger than the proof requires for an already supplied generated positive isometry.

This finite-relative reduction is an application of Henniart (2000), §1.3 Remark, §2.3 Corollary, §2.6 Proposition (a)–(b), and §2.8, printed pp. 441, 445–448. It uses the unitary support already carried by each witness to reach Corollary 2.3.
