# Siegel chamber bounds for split-component orbit vectors

`HasWeightedSiegelChamberGrowth` means that on every weak chamber with compact
right factors a function is bounded by `C B(a) σ(a)^m`. Here `B` is a function of
the positive torus coordinate and `σ(a)` is one plus the logarithm of the
matrix height of its ambient image. The coefficient and degree can depend on
the threshold and compact family.

`AdelicSiegelOrbitGrowthStatement` says that a nonnegative weight `B` is
preserved by the finite complex group-algebra action of the positive split
component. A fixed split-component point centralizes the Levi, so its left
translation commutes with the torus coordinate. The compact right factors
are replaced by their image under this fixed translation. The functions
satisfying the bound form a complex submodule. In the sum estimate the
greater degree works since `σ(a) ≥ 1` for a positive matrix size.

In particular, `hasSiegelChamberGrowth_of_mem_splitComponentOrbitSpan` gives the
ordinary logarithmic Siegel chamber estimate for every vector in the orbit
span by taking `B` to be the square root of the minimal Siegel modulus.
This closure is used when separating the exponent components of a constant
term in the chamber formulation of tempered growth.

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF pp. 11 and 13, Lemma 3.2(c) and Proposition 3.6.
