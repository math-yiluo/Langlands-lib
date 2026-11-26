# Norm-one cuspidal separation from classical approximation

`normOneCuspidalSeparation_of_classicalDensity` proves that
`AdelicNormOneClassicalCuspidalDensityStatement` implies
`NormOneCuspidalSeparationStatement` at arbitrary universe. The proof follows
the compact-smoothing argument of Mœglin–Waldspurger, *Spectral Decomposition
and Eisenstein Series* (1995), I.3.4, p. 46, with the actual norm-one
pairing used in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series* (2024), (6.8), p. 202.

If the input takes a nonzero value at the identity, choose a compact
smooth kernel whose right convolution preserves nonvanishing there. The
convolved function is smooth, cuspidal and of uniform directional height
growth. Rapid decay on the norm-one Siegel cover and finite volume give
its quotient `L²` class. The same bounds for the classical approximants
justify exchanging convolution with the translated pairings. Each
approximant is therefore orthogonal to the class. If the class were
nonzero, an approximant within its norm would contradict Cauchy–Schwarz.
Full support of quotient Haar measure then upgrades vanishing of the
class to pointwise vanishing of the continuous convolved function, giving
a contradiction at the identity.
