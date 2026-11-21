# The descended Gram matrix of a symplectic cocycle

Let the ground field be infinite with `2` invertible, and let the coefficient division algebra be central and finite-dimensional. Its first-kind involution has symmetric dimension `d(d+1)/2`, where `d` is the reduced degree. Let the Gram matrix be invertible and antihermitian with positive size, and let the cover be a finite Galois field extension.

A cocycle of the actual symplectic scheme on this cover has an ambient primitive in the units of the coefficient tensor matrix algebra. The proof maps the cocycle through the actual reduced-norm-one group and applies noncommutative Hilbert 90. The symplectic affine range comparison gives the Gram equation for every cocycle value. Congruence by the inverse of the ambient primitive takes the original Gram matrix to an invertible, skew-adjoint and Galois-fixed tensor matrix. Descent of the fixed ambient unit gives an invertible ground-field matrix. Invertibility of `2` gives the alternating diagonal from skew-adjointness.

`symplecticGramDescent` chooses these data. If an invertible ground-field change of basis takes the original Gram matrix to the descended one, right multiplication of the ambient primitive by that constant unit gives a Gram-preserving unit on the original cover. It lifts to an actual symplectic point. Its coboundary has the original values because the correcting unit is Galois-fixed.

This is the quaternionic form descent used in Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), §5.8, pp. 92–93 (PDF pp. 98–99), in the Library's antihermitian coordinates.
