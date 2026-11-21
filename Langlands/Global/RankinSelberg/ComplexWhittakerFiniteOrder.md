# Finite difference order of complex Whittaker evaluation

Fix an exact intertwiner and its compact approximate identities. Write C
for the common constant and P for the inverse sampling exponent. Set
L = 1 + C, q = 1/(2L), and J = P + 1. At step i use contraction q^i
and let the next residual be the current residual minus its average.

At any difference order each residual step costs at most a factor of L.
From order j + 1 to order j the same step costs at most 2C q^i. For
the residual at step m + J, use the first bound for m steps and the
second for the last J steps. Its uniform compact value bound is at most
L^m (2C q^m)^J times the initial order-J difference bound. The inverse
sampling factor for its average cancels P of the J powers of q^m.
Since Lq = 1/2, the averaged samples in the tail are bounded by a
geometric sequence with ratio 1/2. A finite sum bounds the initial J
samples.

Each residual is a compact-equivariant endomorphism applied to the
initial vector. The finite-dimensional coefficient argument therefore
bounds its identity evaluation by a vector-dependent constant times its
uniform compact value bound. This contribution tends to zero. Apply
linearity at each residual step and take the limit of the telescoping
bound. The resulting order and constant are independent of the vector.
