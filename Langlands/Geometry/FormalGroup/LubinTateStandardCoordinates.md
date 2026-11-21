# Pointed maps intertwining the standard Lubin–Tate polynomial

`polynomialCoordinates` applies the standard polynomial in each coordinate. `Intertwines` records the actual commuting square for a pointed map. It is equivalent to vanishing of the individual series defects and is preserved by composition and pairing.

`liftLinear` realizes a matrix as the tangent coefficients of an actual intertwiner by applying the integral degree recursion to each output. Coefficient uniqueness detects equality of intertwiners from their tangent maps. Coefficient maps fixing the uniformizer preserve the equation and carry the lift of a matrix to the lift of its image.

This gives the form of the standard intertwiner construction used to deduce the formal law identities from their linear terms in Lubin and Tate, *Formal Complex Multiplication in Local Fields* (1965), §1, Lemma 1 and the proof of Theorem 1, printed pp. 381–382.
