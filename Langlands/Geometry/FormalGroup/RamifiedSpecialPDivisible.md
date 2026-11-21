# The actual p-divisible tower of a special formal division module

A special formal division module of central height `d²` has an actual
`p`-divisible group if `p = b * π^e` for a unit `b` and positive `e`.
`IsPiDivisible.unit_mul_pow` proves this passage using the original finite
kernels. Multiplication by the unit is a formal automorphism, and the
`n`-th kernel corresponds to the central scalar kernel at exponent `e*n`.
The two maps act on the original scalar-power points. When `q = p^f`, the
rank of the finite level is `p^(n*e*f*d²)`.

`HeightSquaredModule.pDivisibleAction` restricts the actual division order
action to these finite levels. Given finite Cartier exactness,
`splitPDivisibleGroup`, `splitPDivisiblePolarization`, and
`splitPDivisibleAction` give the product with the full Cartier dual, its
tautological principal polarization, and the exchange-involutive split
order action. The generic adjointness theorem for the split order applies
to these same finite schemes.

The central height condition is that of Drinfeld 1976, §2 A, printed
p. 109 (PDF p. 3). Rapoport–Zink 1996 gives the factor `[F : ℚ_p]` in the
crystal ranks immediately before Definition 3.57, printed p. 109 (PDF
p. 123). The kernel proof derives the corresponding factor `e*f` for the
finite group schemes. The product construction is the one in §6.43,
printed p. 309 (PDF p. 321), before (6.17).
