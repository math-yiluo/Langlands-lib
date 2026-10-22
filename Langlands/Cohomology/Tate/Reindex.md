# Reindexing the actual Tate complex

Author: Worker 45.

For an isomorphism `e : G ≃* H` of finite groups and a coefficient morphism
from the restriction of `A` along `e⁻¹` to `B`, reindexing uses Mathlib's
actual chain map along `e` in negative degrees and actual cochain map
along `e⁻¹` in nonnegative degrees. The coefficient map intertwines in
both directions. Reindexing the finite norm sum by the group isomorphism
proves the compatibility at the splice between degrees −1 and zero.

`reindexComplex` is consequently a map between the existing Tate complexes;
`reindex` is its induced homology map. If the coefficient map is an
isomorphism, every chain and cochain component is an isomorphism, which
proves that the complex and all its homology maps are isomorphisms.
The positive-degree and negative-degree comparison formulas are proved
using Mathlib's homology isomorphisms for the splice. They identify this
map with actual ordinary cohomology reindexing and ordinary homology
reindexing, respectively.

This provides the change of group coordinates needed to state nested
subgroup comparisons without replacing the Tate groups. No transitivity
or subgroup transfer comparison is claimed in this file.

This is an internal coordinate construction for the norm-spliced complex.
Its provenance is Serre, *Local Fields* (1979), Chapter VIII, section 1,
printed pp. 127–129 (PDF pp. 133–135), together with the actual chain,
cochain, and splice constructions in the pinned Mathlib. It is not an
additional assumed functoriality law.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
