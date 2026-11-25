# Rigidity of the numbered E₈ Cartan matrix

This module proves that every self-map preserving all entries of
Mathlib's actual E₈ Cartan matrix fixes every vertex.

Diagonal entries first imply injectivity, hence bijectivity on the finite
vertex set. Starting from the constant color one, three adjacency walk
refinements give the vectors

- `(1, 1, 2, 3, 2, 2, 2, 1)`;
- `(2, 3, 4, 5, 5, 4, 3, 2)`;
- `(4, 5, 7, 12, 9, 8, 6, 3)`.

Each refinement preserves invariance under the given map, by
`CartanWalkColor.step_invariant`. The last vector has distinct entries, so
invariance forces the map to fix each vertex. Ordinary kernel-checked
`decide` verifies the three arithmetic vector equalities and the final
injectivity. This uses no external classification.
