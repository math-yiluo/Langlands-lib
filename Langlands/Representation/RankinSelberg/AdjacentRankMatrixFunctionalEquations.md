# Actual functional equations for the adjacent square factors

Worker 486. This internal prerequisite applies supplied normalized matrix
functional-equation data to the actual determinant-twisted test coefficient
model. It does not impose irreducibility
on either input of the parent adjacent-rank theorem.

`adjacentRankTwistedTestModel` is the literal determinant twist of the
right-translation action on the specified inverse-character coefficient
image. `AdjacentRankMatrixFunctionalEquationWitnesses` records actual
shifted rational values for `Phi,chi(det)*f` and the canonical square Fourier
transform with `chi^-1(det)*coefficientIota(f)`, together with their normalized
functional equation. The fixed polynomials, unit and integer work for every
square test and every actual bi-smooth coefficient. Both original denominator
guards remain in the equation; the supplied self-dual scalar Haar and
canonical group Haar are retained.

The supplied-data theorem constructs the twisted bi-smooth coefficient with
`biSmoothCoefficientTwist`. The normalized data choose a Fourier test before
all coefficients. Its pointwise Fourier identity identifies it with the
canonical square Fourier equivalence. The actual analytic assertions provide
both shifted rational values, and `coefficientIota_determinantTwist` gives
exactly the inverse determinant character in the second value. Applying the
supplied equation to these witnesses proves the result.

The carrier-independent `TwistedTestMatrixFunctionalEquationWitnesses`
records the same assertions for any actual test representation. A private
carrier-independent lemma proves the analytic implication before specializing
to the actual coefficient model. This factoring keeps elaboration from
expanding the concrete coefficient-image action.

All provenance here is internal composition of the named imported proofs.
This module assumes the normalized matrix data; it does not construct them.
It does not construct a generic socle inside a reducible original, compare
its gamma factor with the original, assemble the adjacent finite products,
or continue from a large second twist to an arbitrary character. Those remain
obligations of the parent gamma argument.
