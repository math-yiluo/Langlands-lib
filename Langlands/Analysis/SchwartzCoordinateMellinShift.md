# Coordinate integration by parts for Schwartz Mellin integrals

`coordinateMellin_schwartzCoordinateDeriv` shifts one coordinate of the Mellin exponent by differentiating the test in that coordinate. It applies when all initial real parts are positive.

The proof splits off the selected coordinate by a measure-preserving equivalence for the product measure. Each section of the Schwartz test is Schwartz because the insertion map is an affine isometry. The chain rule identifies its derivative with the section of the coordinate derivative. Fubini and scalar Mellin integration by parts then give the factor minus the initial exponent in that coordinate. The construction is an auxiliary lemma for the local zeta calculation.
