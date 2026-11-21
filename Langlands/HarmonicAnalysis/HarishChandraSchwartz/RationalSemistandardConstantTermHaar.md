# Radical Haar normalization in VIII.2.1

Waldspurger proves that the actual normalized constant term on a proper
Levi vanishes by applying reconstruction on that Levi. The reconstruction
uses the radical measure fixed in the III.6 diagram. The Library's
`RationalCuspidalSemistandardComparisonStatement` expresses vanishing
for every radical Haar measure. [Waldspurger (2003), VIII.2.1, pp. 321–322](https://doi.org/10.1017/S1474748003000082)

`RationalSemistandardCuspidalFromConstantTermHaarStatement` connects these
formulations for an affine, locally finite type connected reductive group
over a nonarchimedean local field. It uses one Haar measure on the literal
rational-point radical of each proper semistandard parabolic and assumes
that `constantTermInd` vanishes for all pairs of translating elements at
that measure. Under the published intrinsic comparison and its closed
matrix embedding hypothesis, it concludes membership in the existing
`rationalCuspidalSubmodule`.

`rationalSemistandardCuspidalFromConstantTermHaar` applies Haar uniqueness on
the closed, locally compact, second-countable radical. The III.6 integral
formula uses the same `semistandardUnipotentModulus` character at either
measure. The Bochner integral at the second measure is the Haar scale
factor times the integral at the first. This factor commutes with the
half-modulus, so the normalized constant term at the second measure is
also zero. This gives the all-Haar vanishing required by the intrinsic
comparison from the normalization prescribed for lower-rank reconstruction.
