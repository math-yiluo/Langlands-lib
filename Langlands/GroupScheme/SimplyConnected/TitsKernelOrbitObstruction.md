# Tits obstructions of full star orbit weights and the actual anisotropic kernel

Author: Worker 5662.

This module proves the obstruction part of clause 3 of Task 7605. Let `G` be simply
connected with actual Tits index data `d` over `k`, and let `p` be the Library's actual
anisotropic kernel. For a simple vertex `a`, the full star orbit weight
`d.absoluteOrbitWeight hsc a` (published module `SimplyConnected/StarOrbitWeights`) is the
sum of the actual integral fundamental weights over the full star orbit of `a`. Module
`SimplyConnected/TitsKernelOrbitWeights` computes its restriction to the kernel torus.
Combined with the comparison of obstructions (module `Reductive/SplitLeviTitsComparison`),
this computes its actual Tits obstruction (Tits, *Représentations linéaires irréductibles
d'un groupe réductif sur un corps quelconque*, J. reine angew. Math. 247 (1971), §5.5–5.6).

## Declarations

- `TitsIndexData.absoluteOrbitWeight_mem_starFixedWeights`: an orbit weight is fixed by the
  full star action (published `absoluteOrbitWeight_star`).
  `TitsIndexData.starFixedOrbitWeight hsc a` is the orbit weight as an element of the
  star-fixed weights.
- `AnisotropicKernelIndex.starFixedRestriction_starFixedOrbitWeight`: its restriction to
  the actual kernel is the explicit restricted orbit weight `p.restrictedOrbitWeight hsc a`
  (`weightRestriction_absoluteOrbitWeight`).
- `AnisotropicKernelIndex.titsObstruction_starFixedOrbitWeight`: the actual Tits obstruction
  of `G` at the orbit weight equals the actual Tits obstruction of the kernel at
  `p.restrictedOrbitWeight hsc a`.
- `AnisotropicKernelIndex.titsObstruction_starFixedOrbitWeight_of_zero`: if `a` is a zero
  vertex, the orbit lies in the zero vertices. The obstruction equals the actual Tits
  obstruction of the kernel at the kernel orbit weight of the kernel vertex
  `p.comparison.vertexEquiv.symm a` (`weightRestriction_absoluteOrbitWeight_of_zero`).
- `AnisotropicKernelIndex.titsObstruction_starFixedOrbitWeight_of_not_zero`: if `a` is not
  a zero vertex, the orbit is disjoint from the zero vertices. The restriction is zero
  (`weightRestriction_absoluteOrbitWeight_of_not_zero`), so the obstruction is zero.

The two cases are exhaustive, by `starOrbitVertices_subset_zero_or_disjoint` (module
`SimplyConnected/TitsKernelOrbitWeights`), which uses the published full star invariance of
the zero vertices. No index admissibility premise is used. Every field and every
characteristic are allowed. The provenance is internal.
