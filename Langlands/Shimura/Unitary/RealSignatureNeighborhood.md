# A neighborhood of a real Hermitian signature matrix

Write J for the prescribed signature matrix. The map on complex
matrices given by X ↦ X + X J X / 4 has identity derivative at zero.
The inverse function theorem gives an inverse near zero. The map commutes
with conjugate transpose because J is Hermitian. For a Hermitian target
near zero, both the inverse image and its conjugate transpose lie in the
neighborhood of injectivity, so the inverse image is Hermitian as well.

The matrix P = 1 + J X / 2 is invertible near zero by continuity of the
determinant. Using J² = 1 and the Hermitian property of X gives
P* J P = J + X + X J X / 4. Thus `signatureCongruenceNeighborhood`
contains J and each of its Hermitian members has the required Gram
congruence.
