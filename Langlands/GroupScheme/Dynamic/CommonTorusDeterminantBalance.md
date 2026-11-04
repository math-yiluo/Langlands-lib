# Dimension-weighted sign balance on a common split torus

This internal deduction concerns the actual adjoint weight spaces of a split
torus in an affine group scheme over an arbitrary field. A region character
sums the characters in a predicate-defined region, each with multiplicity equal
to the dimension of its actual weight space. The locally finite type hypothesis
makes the weight support finite.

The positive-region partition separates the zero, positive and negative values
of a second cocharacter pairing. The supplied `HasRelativeRootSystem` gives
opposite weight-space dimensions through
`HasRelativeRootSystem.finrank_weightSpace_neg` in
`Dynamic.RootSystemDeterminantRestriction`. Reindexing by character negation
therefore negates each region character. The two regions with opposite strict
signs cancel. The resulting balance keeps both zero-pairing axis contributions
and counts the common strictly positive region twice.

This is a character identity on the supplied torus. It does not establish
character detection on a whole common Levi, a Haar-modulus identity there, or
the geometric-lemma expansion. Those remain separate obligations. No
representation theorem or additional structural result is assumed by this
deduction.
