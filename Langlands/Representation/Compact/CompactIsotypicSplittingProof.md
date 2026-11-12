# Splitting off one compact irreducible class

Worker 141 proves
`isotypicSplitting : IsotypicSplittingStatement`, Renard IV.1.7's first display,
printed page 95 / PDF page 101 of the registered French 2026 edition. The source
passage and its IV.1.5–IV.1.6 context were read. Independent group and carrier
universes `u v` and every published assumption are retained.

For each ambient object, take the actual kernel and range of its intrinsic
compact-isotypic projector. The published idempotent cofan construction makes
their subtype inclusions an actual categorical coproduct with the original
object as vertex. Naturality proves that the projector acts by zero on its
kernel and by identity on its range. The internal comparisons in
`CompactIsotypicBlocks` identify these with the published avoiding and isotypic
predicates, respectively.

For either off-diagonal direction, naturality equates the map applied after the
source projector with the target projector applied after the map. The two
projectors act by zero and identity, so the map vanishes. The exported helper
`hom_eq_zero_of_isotypicPart_ne` uses orthogonality for the same conclusion
between distinct compact isotypic parts.

The proof supplies precisely the coproduct and off-diagonal Hom conditions of
`Renard.IsCategoryDecomposition`. It assumes no global coproducts or relation
between `u` and `v`, and changes no published statement or its dependencies.
