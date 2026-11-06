# Canonical continuous cuspidal L2 functions in the full AE carrier

This internal adapter uses the original continuous parabolic-cuspidal L2
space of `GroupSchemeParabolicQuotientL2`, specialized to precisely the
canonical `properParabolicQuotientMeasure` family and the existing
`positiveRationalQuotientHaarMeasure`. It retains the number field, affine
locally finite-type connected reductive group, structural
`ParabolicDynamicStatement`, central split torus, injective finite-index
character restriction and explicit right invariance of norm-one Haar.

A continuous positive-quotient function with all these canonical constant
terms zero satisfies the raw AE cusp condition. Absolute convergence holds
at every norm-one argument by the existing continuous-period theorem.
The exact equality between the positive-quotient period and the original
constant term supplies pointwise vanishing at the same arguments. Thus the
separate AE convergence and AE vanishing conditions both hold.

For a continuous cuspidal L2 function, its existing Lp image agrees almost
everywhere with that function, for the exact same quotient measure.
`mem_aeParabolicCuspidalFunctionSubmodule_congr` transfers the preceding
conditions to this chosen Lp representative, giving membership in the
original full-AE carrier. No pointwise identity of chosen representatives
is used.

`positiveParabolicCuspidalL2ToFullAE` restricts the codomain of the existing
complex-linear intertwiner. The unchanged intertwining law, followed by
subtype extensionality, proves equivariance. Composing with the full-AE
subtype inclusion recovers exactly `positiveParabolicCuspidalL2ToLp`.
Faithfulness follows from the existing full-support result for the
canonical quotient measure. The existing algebraic continuous cuspidal L2
image is consequently contained in the full AE subrepresentation.

The construction derives an inclusion between the two preceding actual
carriers. Its provenance is their already established period comparison,
representative congruence and faithful continuous-to-Lp map. The inherited
source convention is Getz–Hahn (6.18)–(6.21), printed pp.167–168, and its
Section 9.2 with the October 2026 errata, as documented in the imported
modules. No new source theorem is attributed to this adapter. It proves no
equality, surjectivity, density, closedness, automatic square integrability
or smooth automorphic realization.
