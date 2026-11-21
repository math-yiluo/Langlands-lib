# Gamma orders for a unitary supercuspidal pair

`UnitarySupercuspidalPairGammaOrderStatement` applies to two irreducible
unitarizable supercuspidal representations of general linear groups over
the same p-adic field, in arbitrary positive ranks and independent carrier
universes. For their certified symmetric Rankin–Selberg gamma factor, the
spectral function is meromorphic everywhere. Its order is nonpositive off
the imaginary axis. Its order at zero is one if the representations are
contragredient and zero otherwise. Contragredience includes equality of ranks.

The forward L-polynomial is the certified finite product with parameters
on the unit circle supplied by `supercuspidalPairEuler`. A root at the
spectral parameter then requires its absolute value to be one, so the
forward multiplicity vanishes away from the imaginary axis.
`meromorphicOrderAt_rationalGammaExpression` subtracts the reflected
multiplicity, which is nonnegative. At zero, nonvanishing of the reflected
polynomial at `s = 1` removes that term. The product formula and the
contragredience criterion for parameter `1` give the stated order at zero.

The statement is derived from the local pair formulas of
Jacquet–Piatetski-Shapiro–Shalika (1983), Proposition (8.1)(i)–(ii),
printed p. 443 (PDF p. 78), and the p-adic nonvanishing in Getz–Hahn
(2024), Theorem 11.5.2, printed p. 305 (PDF p. 316).
