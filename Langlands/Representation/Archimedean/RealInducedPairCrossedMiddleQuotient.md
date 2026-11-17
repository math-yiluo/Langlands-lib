# The actual crossed quotient of the positive-inner mixed source

This internal construction applies the negative-inner quotient to the crossed
endpoint pair. It uses the actual quotient proved in
`RealInducedPairNegativeInnerQuotient` and the crossed arithmetic, without any
additional literature premise.

For positive original absolute weights `L,M`, a linked index `k`, and positive
signed inner weight `H`, choose the original endpoint parities
`sd=L%2` and `se=H.toNat%2`. They satisfy the outer singular parity condition
used by `RealInducedPairDistantParity`. Let `u,v,x,y` be the lower and upper
endpoints of `d,e` with those parities.

The crossed pair has weights `A=L+H`, `B=M+H` and negative signed inner weight
`-H`. Its negative-inner quotient uses left parity `(H+A)%2=L%2`.
Its middle-induced source is exactly the original mixed source
`[character u, induced(pairInduced v x H.toNat), character y]`.
The proof checks both outer character parities, their exponents, and the
central induced datum.

Transporting the negative-inner quotient across this equality gives an exact
surjective intertwiner from that actual mixed module onto the crossed pair.
The transport is the identity on underlying functions. The mixed source can
be lighter than the original pair, whereas the crossed target is heavier.
The kernel is the pullback, under the actual inclusion into the crossed
four-character presentation, of the sum of the two crossed binomial images.
This follows from factorization through the published crossed quotient and
its two-binomial kernel theorem.

`RealInducedPairCrossedMiddleQuotientStatement` asserts the original outer
parity condition and exactness and surjectivity of this explicitly constructed
quotient, for every linked pair with positive original absolute weights and
positive signed inner weight. Its theorem proves this proposition.

This map alone does not replace the mixed source in the original filtration.
One must still prove that its kernel maps into the preceding allowed source
ranges under the map to the original pair. No such kernel inclusion, descent
to the original target, or unrestricted filtration is asserted here.
