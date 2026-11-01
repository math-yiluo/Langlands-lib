# Weighted convergence of the actual compact model average

This internally derived step applies Iwasawa unfolding to the actual original
model vector produced by compact corner averaging. If the shifted matrix
integrand is absolutely integrable, unfolding supplies joint integrability in
the rank-one and tail parameters. Fubini then gives integrability of the tail
integral as a function of the rank-one variable. The pointwise corner-average
identity identifies that function with the restriction of the same averaged
vector, multiplied by the determinant weight.

The density `|det g|^(-n)` in the rank-one Iwasawa measure changes the matrix
weight at `s+n/2` to the rank-one weight at `s-n/2`. Removing that density using
the actual with-density integration theorems proves both absolute convergence
and equality of the matrix and rank-one integrals. This uses the full product
integrability supplied by unfolding, rather than inferring absolute convergence
from a scalar equality.

The existential endpoint retains one universal compact kernel before all input
vectors, the original coefficient model and functional, the supplied self-dual
scalar measure, and the actual right-average formula at every group element.
The chosen averaged vector is independent of the spectral parameter. The result
holds for every positive rank and independent field and carrier universes. It
does not yet identify the dual integral or prove the paired gamma comparison.

`weightedCornerAverage` selects this original-model vector using the universal
kernel before the input vector. Its comparison theorem retains the actual
weighted convergence and value identity at every admissible spectral parameter.
