# Scalar comparison with fixed factors in the composition law

`roundTripScalar_mul_of_scaled_composition` evaluates the round trip
through three carriers in two ways. Using the forward and reverse
composition gives the direct scalar times the two composition factors.
Using the given scalar on each consecutive pair gives the product of
those scalars. A nonzero test vector in the first carrier identifies the
coefficients.

`oppositeScalar_mul_of_scaled_composition` implements the comparison of
opposite scalars from Waldspurger IV.3(1), printed pp. 285–286, for
compositions that carry fixed scalar factors. The four composition
identities rewrite the same chain of five maps. Applying the chain to a
vector with nonzero image under the first map gives the stated equality
of products. This is the linear-algebra step in the argument. In the
application to actual standard intertwiners the composition factors
come from the specified Haar measures.

Source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
