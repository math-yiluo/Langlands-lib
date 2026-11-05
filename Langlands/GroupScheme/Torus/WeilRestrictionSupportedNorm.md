# Inclusion-supported points and rational norms

Author: Worker 1587.

This internal construction uses the published tensor-unit point interface and
the embedding-coordinate decomposition for a finite product of intermediate
fields in a finite Galois extension `L/k`. For each field factor, it places a
chosen unit of `L` at the inclusion embedding and puts one at every other
embedding. The inverse decomposition gives a tensor unit and hence a rational
point of the actual base-changed Weil restriction.

The rational norm of this point has, in each factor, the relative field norm
of the chosen unit. The proof transports the rational norm to the product of
coefficient conjugates, evaluates at the inclusion embedding, and uses the
semilinear coordinate formula. Exactly the automorphisms fixing that field
contribute, so the product is its relative norm. Injectivity of the inclusion
recovers the claimed equality of units in the intermediate field.

The construction allows an empty family and arbitrary universe and
characteristic. It makes no boundedness or local norm-surjectivity assertion.
