# Tate weights for the complex Godement diagonal

At a diagonal position occupied by the smaller inducing character `e`, the
ratio of the added character `d` to `e` has angular weight
`d.weight - e.weight` and exponent `d.exponent - e.exponent`. The triangular
integral adds one normalized modulus power, giving the Tate parameter
`d.exponent - e.exponent + 1`. Passing to complex additive Lebesgue measure
multiplies by the inverse squared norm. In the Lean identity this density
cancels the first modulus power from `diagonalTateWeight`, leaving the
families of Tate powers `‖z‖ ^ (2 * u - 2)` on the additive space.

[Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, proof of Proposition 7.1, p. 44](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
