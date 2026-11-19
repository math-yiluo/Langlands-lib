# Compact-uniform moderate growth in the normalized adelic height

The normalized adelic matrix height is at least one for positive matrix
size. `adelicHeightAtLeastOne` extends that lower bound to size zero by
replacing values below one with one. The original source norm differs from
the normalized height by a positive scalar for positive matrix size.
Extracting this scalar from the original power allows the growth exponent
to be increased to a nonnegative exponent.

Continuity bounds the normalized height on a compact set of right
translations. The product bound for the normalized height then gives
one moderate-growth bound on all these translates, with the same growth
exponent for every compact set. For size zero the matrix image is constant,
so the supplied moderate growth bounds the function globally.

This internal estimate uses the Library's actual adelic source norm and
moderate-growth predicate. It supplies the compact-translate growth
estimate for the absolute convergence theorem of Mœglin–Waldspurger II.1.5.
