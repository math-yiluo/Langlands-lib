# Height bounds for the actual unitary Laurent coordinates

`RationalValuationCoordinateHeightStatement` bounds the sup norm of the
valuation coordinates of an actual rational point by a constant times
one plus the height of a closed matrix realization. The valuation
coordinates are those used to evaluate a unitary unramified character
in the canonical circle coordinates.

The proof evaluates the integer valuation image on a basis of the
rational character lattice. The resulting integer-linear map is
injective. Extension of scalars to the reals preserves injectivity,
and a continuous linear left inverse controls the sup norm. The
published height bound for each rational-character valuation and the
finiteness of the basis then give a single bound.

`LeviModel.exists_laurentExponent_height_bound` applies the estimate
to any literal semistandard Levi. The transported unitary characters
identify its Laurent exponents with the valuation coordinates of the
representing scheme. Restricting the closed matrix model along the
Levi inclusion preserves closedness and gives the restricted ambient
height. This supplies the Laurent height field of the semistandard
Fourier analytic inputs for that choice of height.

[Waldspurger (2003), I.1 and VII.1.3, printed pp. 239–242 and 316–317](https://doi.org/10.1017/S1474748003000082)
