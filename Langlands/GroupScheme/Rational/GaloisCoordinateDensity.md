# Density of three Galois coordinates

`galoisTripleCoordinateDensity` works with a connected reductive group
over an infinite field and a finite Galois extension. For three distinct
automorphisms of the extension, it forms the three Galois translates of
each point over the extension and right-translates each coordinate by a
fixed rational point. The resulting tuples are Zariski dense in the
cube over the extension.

The proof identifies the scalar extension of the affine Weil restriction
with the product indexed by the field embeddings. It matches the product's
coordinate maps with evaluation at those embeddings on the scalar
extensions of rational points. Over the ground field the Weil
restriction is connected reductive, so unirationality gives density of
its rational points over the infinite field. The density passes to the
scalar extension. Projection to three distinct factors, followed by the
three translations, is a surjective morphism, and its image of this
dense set gives the required tuples.

The result implements the density step for choosing three conjugate
parabolics in the cyclic construction of Platonov and Rapinchuk,
*Algebraic Groups and Number Theory* (1994), §6.8, printed p. 372.
