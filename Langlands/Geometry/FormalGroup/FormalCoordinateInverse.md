# Formal inversion with identity linear part

The split formal image used in the Rapoport–Zink construction requires coordinates on the fixed points of actual order idempotents. This module develops the formal inverse calculation needed to construct those coordinates.

Subtracting substitution by a tuple with identity linear part from the identity operator raises degree by one. In each monomial the difference of the two substitutions can be written as a sum of terms containing one higher-order difference of coordinates. The coefficient formula for substitution extends this calculation to arbitrary power series. The degree condition follows from the identity tangent by evaluating its matrix on the coordinate vectors.

Substitution is injective because any element in its kernel is fixed by the degree-raising correction. It therefore vanishes in every degree. To invert substitution on a series, sum the iterates of that correction applied to the series. Each coefficient stabilizes after finitely many terms. Continuity of substitution and the shift of the summation index give a preimage of the original series.

`CoordinateMap.inverseOfIdentityLinear` applies the inverse algebra map to each coordinate variable. Its series have zero constant term, and the two composition identities give a pointed formal inverse.
