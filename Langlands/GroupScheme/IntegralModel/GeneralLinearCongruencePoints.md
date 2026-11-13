# Matrix coordinates of the standard congruence subgroup

This internal companion identifies the actual congruence condition for the
standard general linear integral model with the entrywise matrix condition.
For every positive level k, the difference of each entry from the identity
must lie in the kth power of the actual maximal ideal.

`standardCongruencePoint` takes an invertible matrix over the integral base
satisfying those conditions and returns a point in the original generic
congruence subgroup. Its matrix is exactly the image of the supplied matrix
under the original fraction-field inclusion.

The proof first shows that restriction of a general linear section applies
the coefficient homomorphism to its matrix. This follows from the published
base-change entry formula, the projection of the restricted section, and
naturality of global sections of affine spectra. Applying this to the actual
maximal-ideal-power quotient identifies the reduction kernel entry by entry.
The constructor then uses the original standard integral-point map.

The provenance is internal composition of the standard general linear model,
its published matrix comparison and the actual congruence tower. No claim of
an arbitrary lattice model or of a maximal pro-p classification is made here.
