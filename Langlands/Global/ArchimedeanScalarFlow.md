# Real sign representatives and scalar Lie flows

`mixedRealSignUnit` assigns a unit of the mixed archimedean algebra to each choice of signs at the real places, with value one at every complex place. Every unit in mixed coordinates is a product of such a sign unit and an exponential. The exponential argument uses the logarithm of the absolute value at real places and the complex logarithm at complex places.

`scalarDirection` is the real Lie direction represented by a scalar matrix over the mixed archimedean algebra. It commutes with every matrix direction. Its complexification commutes with the complexified Lie algebra, so `scalarDirectionCenter` is its image in the enveloping centre.

Applying the matrix scalar map to the convergent exponential gives the matrix exponential of the scalar direction. Under the ring equivalence between mixed coordinates and infinite adeles, this identifies the actual infinite adelic Lie flow with scalar multiplication by the corresponding exponential unit. This is an internal coordinate calculation for the block idele centre orbit in Task 6823.
