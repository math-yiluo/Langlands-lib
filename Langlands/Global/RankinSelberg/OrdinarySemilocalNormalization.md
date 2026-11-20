# Normalizing an ordinary partial Whittaker integral

`OrdinaryIntegralNormalization` records an entire function whose product
with the given local L-factor equals the ordinary integral on a right
half-plane. Finite products of these records use the largest of the
finitely many local half-plane thresholds, or any real upper bound for
them. A finite product of the entire values is entire.

`exists_normalization_of_semilocal_pointwise_product` starts with a
pointwise product of the ordinary local kernels at the real and complex
places and the places in the finite set `S`. The kernel is integrated
over the class set used by both ordinary partial Whittaker integrals.
The published quotient-measure formula identifies the integral of this
product with the product of the local integrals times one nonzero
constant. The normalized value is the product of the local values,
multiplied by this constant and the nonzero pointwise scalar. The
explicit equality for this value lets the consumer carry pointwise
nonvanishing through the product.

This is the ordinary factorization step in J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §4.1, printed pp. 219–220
(PDF pp. 222–223), and the use of normalized factors in §4.2, printed
p. 222 (PDF p. 225). The local normalized values and the pointwise
kernel identity are explicit inputs. The Lean proof supplies their
measure-theoretic and analytic transfer to the partial integral.
