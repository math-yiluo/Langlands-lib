# The source radical inside the full stabilizer kernel

This internal adapter uses the literal source-radical intersection equality
in `GeometricLemmaIntersectionDatum`. It constructs one direction of the
stabilizer-kernel image comparison without a dynamic or root presentation.
The ambient rational point group has its canonical topology and the original
local-field and represented parabolic hypotheses.

Let `H = Q ∩ z⁻¹Pz`, viewed inside `pointImage q`, and let `πQ` be the original
target Levi projection. The subgroup `NQH` is exactly
`πQ.ker.comap H.subtype`. For a point `m` of
`pointImage (D.r' ≫ D.p')` in the original source Levi's own points,
`sourceRadicalToStabilizer` sends it to
`z⁻¹ * rationalPoints.map (l ≫ p) m * z`. The supplied literal source-radical
equality says that this conjugate lies in the original target radical.
Its conjugate back is an original source Levi point, hence belongs to the
source parabolic. These two facts put the point in `H`.

`sourceRadicalToStabilizer_mem_kernel` proves that the lift lies in `NQH`,
using the exact kernel characterization of the original target semidirect
projection. `sourceRadicalToStabilizerKernel` retains this membership in the
codomain. The projection identity
`stabilizerToLeviPoints_sourceRadicalToStabilizer` first cancels the conjugation,
then uses the original source projection's section law and the actual
`leviPointsEquiv`. Thus it recovers the same point of the source Levi.

Consequently `sourceRadical_le_stabilizerKernel_image` proves that the actual
source intersection radical is contained in the image of `NQH` under
`stabilizerToLeviPoints`. The reverse inclusion is not asserted or assumed
here. This module does not prove full stabilizer projection preservation,
the image equality, or the closed normalized orbit comparison. Its
provenance is the original intersection datum, the literal-point adapter,
and the original semidirect section identities.
