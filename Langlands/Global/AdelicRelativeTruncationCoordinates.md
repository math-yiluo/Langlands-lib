# Relative coroot coordinates of the truncated Eisenstein pairing

Delorme, *On the spectral theorem of Langlands* (2023), uses the projection
from the minimal split space to each parabolic split space in §2 and (7.8)–(7.12).
The kernel consists of the coroot directions of the parabolic Levi. In
`ker_splitDual`, the standard parabolic and the compatible family member
represent the same subgroup, so their isomorphism identifies the two
restriction maps from the maximal split torus. The corresponding maps on
character duals differ by the dual of that parabolic isomorphism. The kernel
therefore follows from `parabolicSpacesComparison`. In particular, the split
logarithm is invariant under taking the level projection.

`splitDual_eq_sum_relativeCoroot` expands a vector of the relative coroot
space in the full simple coroot basis and applies the split logarithm.
The coroots in the Levi are in its kernel. The finite sum of the remaining
terms is the claimed projected expansion.

The coefficients used by `UnitaryPairingExpansion.regularizedConeIntegral`
are the full fundamental weights indexed by simple roots outside the Levi.
Inverse-Cartan positivity gives a positive value at each such root on any
strictly dominant direction. Linearity makes each coefficient grow linearly
on its ray. This supplies the positive translation slopes in the cone limit
of Delorme's Lemma 7.11.
