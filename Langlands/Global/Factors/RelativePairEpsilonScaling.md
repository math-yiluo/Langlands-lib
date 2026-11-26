# Change of additive character on the relative isometry graph

`Langlands.Global.PoleComparison.relativePairEpsilonScaling` proves that a common virtual Weil and JPSS epsilon certificate for one nontrivial additive character gives a common certificate for any other nontrivial additive character, using a self-dual measure for each. This is the character-change step for `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.

`epsilonCorrection` gives the integer-bilinear map for the change of coefficient and exponent under \(\psi(x)\mapsto\psi(ax)\). The coefficient acquires the two determinant or central-character values raised to the respective partner degrees and the half-density term. The exponent acquires the product of the degrees times \(\operatorname{ord}(a)\).

On the Weil side the basis calculation is `Correspondence.isArithmeticPairEpsilonFactor_zeroMonodromy_scale`. On the JPSS side it uses `RankinSelberg.equalRankEpsilonCharacterChange` and `RankinSelberg.pairFactorCharacterChange`. Uniqueness of basis certificates makes these formulas identities of bilinear maps.

`exists_unit_scale_eq` represents the second character as a scaling of the first. The bottom reciprocity candidate of the supplied system is geometric by `isGeometricReciprocity_of_isBaseReciprocity`. `reciprocityHom_surjective` lifts the scaling unit to a Weil element. `pairedLattice_determinant` and `relative_graph_mem_pair` then identify the determinant values with the central-character values. Degree preservation gives equality of the corrections. This implements the change of character in Henniart (2000), §1.3, printed p. 441.
