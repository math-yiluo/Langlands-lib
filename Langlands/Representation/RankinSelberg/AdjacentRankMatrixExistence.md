# Matrix equation existence for adjacent test coefficients

Worker 486. This internal composition proves
`exists_adjacentRankMatrixFunctionalEquationWitnesses`. For a specified
irreducible full Whittaker-type test representation, a nonzero specified
inverse-character functional and any quasicharacter, it constructs
polynomials `P, PD`, a complex unit `c` and an integer `a` with actual
normalized matrix functional-equation data on the determinant twist of its
coefficient-image representation. It also supplies the literal original and
unreflected dual shifted-value witnesses defined in
`AdjacentRankMatrixFunctionalEquations`.
`AdjacentRankMatrixFunctionalEquationExistence` is the Prop-valued
specification of this conclusion.

The field and test-carrier universes are independent. The canonical p-adic
structures, supplied unitary additive character, supplied self-dual additive
Haar measure, canonical group Haar measure and actual square Fourier
transform are retained throughout.

The proof uses the actual model equivalence `modelEquiv` for a nonzero
functional on an irreducible representation. All three clauses of full
Whittaker type transfer along it. The standard character of the additive
character scaled by minus one is the inverse standard character; the
published standard/inverse full-type equivalence converts it back to the
standard convention on this same coefficient image. Representation
equivalence also transfers irreducibility.

A carrier-independent helper twists a standard full-type irreducible test
by the determinant quasicharacter. The published full-type twist theorem
and the actual subrepresentation-lattice twist equivalence preserve full
type and irreducibility. The published `genericMatrixFunctionalEquation`
then constructs the normalized analytic data for this actual twisted
representation. Finally,
`adjacentRankMatrixFunctionalEquationWitnesses_of_data` supplies the exact
shifted values and their Fourier equation, with the same polynomials and
constants for every square test and every actual bi-smooth coefficient.
Carrier-independent helpers and explicit carrier parameters prevent a
character conversion from rewriting the dependent coefficient-image type.

The provenance is internal composition of these imported proofs. No new
literature translation is asserted. This result assumes irreducibility only
of the chosen test representation. To apply it inside the arbitrary-input
adjacent-rank gamma argument, the parent still must choose a genuine
irreducible generic submodel, compare factors with the original full-type
inputs, assemble the matched finite products and continue from large second
twists. This result alone proves none of those remaining steps.
