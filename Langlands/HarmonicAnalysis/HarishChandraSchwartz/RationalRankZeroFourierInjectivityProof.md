# Proof of local Fourier injectivity in relative semisimple rank zero

`rationalRankZeroFourierInjectivity` proves
`RationalRankZeroFourierInjectivityStatement` at the independent field and
representation-carrier universes. It uses the given matrix height, ambient Haar
measure and split-central quotient measures of the actual Fourier family.

Weil disintegration of the ambient square weight gives a split-center coset
with a representative \(g\) on which the weight has finite integral. The
spherical function satisfies \(\Xi(ag)=\Xi(g)>0\) for every split-central
point \(a\). Subadditivity gives
\(1+\sigma(ag)\le (1+\sigma(a))(1+\sigma(g))\). For the nonnegative
exponent \(d\) in the ambient estimate this bounds
\((1+\sigma(a))^{-d}\) by a finite positive multiple of the coset
integrand. This supplies `CentralWeights` for the given height.

The relative rank is independent of the maximal split torus. Rank zero
makes that torus central, so the Fourier data's maximal split torus is
a split component. There are no proper constant terms, and the
rank-zero finite-dimensionality theorem applies to all projected
cuspidal levels. At the full standard index the split-center comparison
identifies the quotient subgroups. Evaluating the zero Fourier family
at the orbit and representative of each inducing discrete series
gives its zero Fourier tensor. `rationalFullLeviFourierActionVanishing`
compares the supplied Levi quotient Haar measure with the ambient
quotient Haar measure and gives vanishing of every discrete-series
action on the inverted function. The weight-based cuspidal separation
theorem then applies the coefficient inclusion and Fourier uniqueness
on the split center.

This is the rank-zero case of the zero-Fourier argument in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, 2003, VIII.5, printed p. 332 (PDF p. 98).
The retained source `waldspurger-2003-plancherel` has SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
