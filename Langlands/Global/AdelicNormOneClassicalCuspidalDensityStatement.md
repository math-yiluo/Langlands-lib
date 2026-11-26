# Norm-one approximation by classical cuspidal functions

`AdelicNormOneClassicalCuspidalDensityStatement` is the approximation
statement used for the norm-one cuspidal vanishing argument. The input is
a rationally invariant smooth cuspidal function whose archimedean real
derivative words are bounded by one common exponent of the adelic matrix
height. For every positive error, it asks for a cuspidal function satisfying
`IsAutomorphicFunctionOn` for the given compact subgroup and matrix
representation, with uniform directional height growth and with norm-one
restriction within the error in the quotient `L²` seminorm.

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.3.4, p. 46, uses density of the classical cusp forms in the cuspidal
Hilbert space after smoothing a continuous input. The norm-one quotient
comes from the Levi tests of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series* (2024), (6.8), p. 202. The formulation
here uses the derivative condition of the adelic relative rapid-decay
theorem so that the approximants also give the absolute bounds for the
pairing of a translate of the original input.
