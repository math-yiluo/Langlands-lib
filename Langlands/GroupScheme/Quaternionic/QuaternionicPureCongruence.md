# Congruence of pure quaternion values by rescaling

`QuaternionicPureCongruenceStatement` works over a field of characteristic zero with a central quaternion division algebra and over any extension field `R`. Its conjugation and norm are the actual scalar-extended quaternion conjugation and reduced norm. The coefficient algebra over `R` may be split.

Take a pure unit `x` and a pure value `y`. If `N(y) = s² N(x)` with `s ≠ 0`, put `z = s⁻¹ • y` and `g = 1 + z * x⁻¹`. When `N(g) ≠ 0` and `s / N(g)` is a square in `R`, there is a unit `u` with `u * x * τ(u) = y`.

Indeed, `z² = x²` by the pure quaternion norm identity. Expanding gives `g * x = z * g`. Scale `g` by a square root of `s / N(g)` to obtain a unit of norm `s`. Its conjugate product is the scalar `s`, so the congruence sends `x` to `s • z = y`.

This is an explicit algebraic criterion for the approximation argument in Springer's appendix to Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), Lemma 5.3.4(b), printed p. 111 (PDF p. 117). The statement uses the two square conditions on this chosen multiplier.
