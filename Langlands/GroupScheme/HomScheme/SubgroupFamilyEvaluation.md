# Composition of actual subgroup-family evaluation

Author: Worker 1656.

This internal unit proves composition for the actual family evaluation
of `TorusSubgroupModuli`. It is valid in arbitrary universe `u` for any
actual subgroup-family homomorphism. Neither closedness nor the
relative-torus condition is needed.

`familyHom_original` computes the projection of an evaluated inclusion
to the original ambient group scheme. It is the projection from the
pulled-back source, followed by the original inclusion and the original
ambient projection. The proof uses the ambient pullback-comparison
projection formula and the defining pullback map.

`familyHom_evaluate_comp` compares evaluating first along `a : T → M`
and then `b : U → T` with evaluation along `b ≫ a`. The left source is
an iterated pullback of `K`, whereas the right source is the direct
pullback. The definition `familySourceComparison K a b` is the actual
isomorphism `Descent.pullbackComparison a.left b.left (b ≫ a).left rfl K`.
Precomposition with it gives
equality of the actual homomorphisms. The proof compares their two
underlying pullback projections. Projection to the original ambient
group uses `familyHom_original` twice and the source comparison
identity; projection to the new base uses that the morphisms are over it.

`evaluate_comp` then removes this source isomorphism from the actual
range using `SubgroupFunctor.range_iso_comp`. It establishes equality
of subgroup functors on every scheme over `U`, rather than only an
isomorphism between representing group schemes or agreement on field
points. No moduli scheme or representability theorem is asserted.
