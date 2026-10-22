# Comparing ordinary cochains with the actual Tate complex

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The auxiliary zero splice retains Mathlib's ordinary chains and cochains but
sets the connecting differential to zero. It is used only to construct
comparison chain maps; all advertised Tate operations still have Mathlib's
actual Tate cohomology as their source and target.

An ordinary cochain pullback along a group homomorphism extends to a map from
the zero splice to the actual Tate complex by taking zero on the negative
chain terms. The splice compatibility is then a proved zero equality.
Mathlib's splice comparison theorem identifies its positive-degree homology
map with the actual ordinary cohomology map. At degree zero, proved kernel
and cokernel data identify the source with invariant elements, and the
comparison sends an invariant to its class modulo the actual norm image.
The comparison is therefore surjective in every nonnegative degree.

The zero splice is exact as a coefficient functor because its evaluations
are the ordinary chain and cochain functors. A map of coefficient short exact
sequences consequently gives a map of short exact complexes, proving the
connecting-map comparison by Mathlib's naturality theorem.

This is an internal comparison construction for Serre's Tate conventions:
*Local Fields* (1979), Chapter VIII, sections 1–2, printed pp. 127–130
(PDF pp. 133–136). It prepares, but does not by itself assert, the comparison
of the dimension-shifted subgroup maps with ordinary cohomology.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
