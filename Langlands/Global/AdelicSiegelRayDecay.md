# Decay in a simple-root logarithm on a Siegel chamber

`AdelicSiegelRayDecayStatement` assumes `IsSiegelAlgebraicSetup` and an
adelic matrix height from a representation of positive dimension. The weak
chamber lies in the intrinsic positive subgroup of the maximal split torus
of the derived group. Its inequalities use the simple roots of the ambient
maximal split torus restricted to this derived torus.

The statement assumes compatibility of nested half moduli, a finite
normalized exponent decomposition at a specified standard parabolic, and
logarithmic chamber growth for the function on the ambient adelic group.
The supplied ray is represented in the specified split component and has a
positive step at one simple root and zero steps at the other simple roots.
Its nonnegative integer powers belong to the weak chamber with threshold one.
Every nonzero normalized component has character norm below one on that
ray. For each fixed positive threshold and compact set of right factors, the
bound on the weak chamber is the square root of the Siegel modulus times a
power of one plus a common nonnegative upper bound for the simple-root
logarithms, with an exponential decay factor in the selected logarithm.
The constants are uniform in the chamber point, right factor and upper bound.

The orbit bound gives logarithmic chamber growth for each exponent
component. Along the ray, after dividing by the ordinary eigencharacter,
the component values are polynomial in the integer parameter. Finite
interpolation bounds their coefficients from chamber values at finitely
many samples. A common rate strictly between the largest nonzero component
norm and one absorbs all the polynomial factors in the integer parameter.
Factoring a chamber point into an integer ray power and a residual point
keeps the residual point in the chamber. Its simple-root logarithms are
bounded above by those of the original point, and the chamber threshold gives
a lower bound. The restricted simple roots span the rational character
space of the derived split torus. The height comparison therefore bounds
one plus the logarithmic height of the residual point linearly in one plus
the common upper bound. The floor estimate turns the geometric factor into
exponential decay in the original root logarithm.

Delorme's (3.2) gives the normalized exponent model. Proposition 3.6
derives subunitarity from a growth estimate. Lemma 3.10(i) derives strictness
from the vanishing of weak constant terms and then applies a square
integrability criterion. The theorem here takes strictness on one ray as a
hypothesis and derives its uniform pointwise decay estimate by finite
interpolation.

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF pp. 10, 13 and 15–16.
