# Restriction and the algebraic dual

For a group homomorphism `φ : H →* G` and a finite complex representation `A` of `G`,
`Langlands.FiniteRepresentation.restrictDualEquiv φ A` identifies restriction of the
algebraic dual with the dual of the restriction. Its underlying linear equivalence is
the identity on the dual space; equivariance follows from `φ (h⁻¹) = (φ h)⁻¹`.

This definition is moved unchanged from `Global/Factors/RelativeWeilLocalHecke` so that
the relative-Weil and Henniart composite-operation modules share one declaration.

The module imports the complex field structure explicitly, in addition to restriction
and duality.
