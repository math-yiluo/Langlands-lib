# Based root data with spanning coroots are determined by their Cartan matrix: proof

Proof author: Worker 61 (Task 5703).

This module proves `Langlands.LinearAlgebra.CorootSpanCartanEquivStatement` (module
`Langlands.LinearAlgebra.CorootSpanCartanEquivStatement`). The theorem is
`Langlands.LinearAlgebra.corootSpanCartanEquiv`, at universe parameter `u`, with no
added hypotheses. Its axioms are only `propext`, `Classical.choice` and `Quot.sound`.

The statement: let `P` and `Q` be finite reduced root data over `ℤ` whose coroots span
the coweight lattices, with bases `b` and `c`. Let `e : b.support ≃ c.support` preserve
all simple pairings. Then some `f : RootPairing.Equiv P Q` satisfies
`f.indexEquiv i = e i` on `b.support`.

## Proof

The theorem introduces the data and applies
`Langlands.RootDatumSimpleCorootEquiv.exists_equiv_indexEquiv` from the helper module
`Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv`. That module's Markdown has the
details. In outline:

1. Since the coroots span, the simple coroots of `b` and of `c` are `ℤ`-bases of the
   coweight lattices (`simpleCorootBasis`). The coweight isomorphism `g` matches the
   two bases along `e`.
2. The weight isomorphism `f` is the transpose of `g⁻¹` through the perfect pairings.
   So `f` and `g` are adjoint. Because `e` preserves the simple pairings and the simple
   coroots of `c` separate weights, `f` sends each simple root to the simple root
   indexed by `e`.
3. Every root and coroot comes from a simple one by simple reflections (Mathlib's
   `RootPairing.Base.induction_reflect`). Adjointness and the reflection formulas then
   show that `(f, g)` sends each root–coroot pair of `P` to a pair of `Q`. The same
   holds for `(f⁻¹, g⁻¹)` from `Q` to `P`. The two index maps are mutually inverse by
   injectivity of the roots, and together with `f` and `g⁻¹` they form the required
   `RootPairing.Equiv`.
