# Comparing ordinary cochains with the actual Tate complex

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation. Worker 25 clarified
the general comparison and the identity specialization.

The auxiliary zero splice retains Mathlib's ordinary chains and cochains but
sets the connecting differential to zero. It is used only to construct
comparison chain maps; all advertised Tate operations still have Mathlib's
actual Tate cohomology as their source and target.

For a group homomorphism `f : H →* G` and coefficient morphism
`φ : Rep.res f A ⟶ B`, `cochainsToTate f φ` extends ordinary cochain pullback
to a map from the zero splice to the actual Tate complex by taking zero on
the negative chain terms. The splice compatibility is a proved zero equality.
Mathlib's splice comparison theorem identifies its positive-degree homology
map with the actual ordinary cohomology map. At degree zero,
`zeroSpliceZeroEquiv A` identifies the source with `A.ρ.invariants` and
`cochainsToTate_zero_hom` identifies the map with
`cochainInvariantMap f φ` followed by `zeroClass B`: first apply the group
and coefficient pullback to the invariant representative, then take its
class modulo the target norm image. These general comparison formulas
require `[Fintype H]`; they do not require `[Fintype G]`.

For the canonical comparison on the same finite group, with
`f := MonoidHom.id G` and `φ := 𝟙 A`, the theorem
`cochainsToTate_surjective` proves surjectivity on homology in every
nonnegative degree. In positive degrees `cochainsToTate_homology_id` and
`cochainsToTateIso` identify it with an isomorphism. At zero it is the
surjective class map from invariants to invariants modulo norms.
No surjectivity assertion is made for arbitrary `f` and `φ`.
The declarations retain the arbitrary common universe `u`, commutative
scalar ring `R`, and general representations; the coefficient action need
not be trivial.

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
