# Leading transverse coefficients under a local pullback

A distribution has transverse order at most \(i\) when it annihilates
every test whose transverse derivatives through order \(i\) vanish on
the zero section. A distribution supported on that section has such
an order after restriction to an open product contained in a compact
subset of the original product domain. This follows from the
fixed-support distribution bound and the flat-test theorem.

For a distribution of order at most \(i\), its evaluation on a test
whose derivatives of orders below \(i\) vanish is the leading
coefficient functional evaluated on the order-\(i\) derivative.
Subtracting a single-order extension of that derivative leaves a
test annihilated by the order bound. Consequently, if the leading
coefficient vanishes, the order drops by one. At order zero this
vanishing gives the zero distribution.

Suppose a continuous pullback of tests has the germ of composition
with a map \(H\) smooth at each point \((x,0)\) of the source zero
section, with \(H(x,0)=(b(x),0)\). Extending an order-\(i\) coefficient,
pulling its extension back and extracting the order-\(i\) derivative
gives a continuous pullback of coefficient tests. On a symmetric
coefficient its value at \(x\) is the coefficient at \(b(x)\)
evaluated on each normal vector after applying `productNormalDerivative H x`.
The pulled-back extension has zero derivatives of all lower orders.
The leading coefficient of the transported distribution is thus the
original leading coefficient composed with this coefficient pullback.

This internal construction supplies the local covariance law and
the order-lowering step for distributions supported on a stratum
given by a product chart.
