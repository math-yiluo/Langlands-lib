# Pullback comparisons normalized on a common refinement

This is a derived construction for actual module sheaves on schemes. It uses
Mathlib's module pullback functors and their canonical composition comparisons,
together with the published `compHom`, `squarePullbackIso`, and
`CommonSourceCocycle` coherence lemmas. It makes no assertion from external
literature.

Given maps `q : V → K`, `a : K → A`, and `f : V → A` with `q ≫ a = f`,
and an isomorphism `e : a* M ≅ N`, `normalize` constructs the actual isomorphism
`f* M ≅ q* N`. Its first factor is the inverse canonical comparison between
iterated pullback and pullback along the specified composite; its second factor
is `q* e`.

For two pieces `M` on `A` and `N` on `B`, maps from `K` to both schemes,
and identifications of both pulled-back pieces with one module `P` on `K`,
`transition` compares their pullbacks on `V`. It normalizes the first piece to
`q* P` and then applies the inverse normalization of the second piece. The maps
and their factorization equations are explicit arguments. Neither a global
module nor a descent cocycle is an input.

`normalize_refine` proves compatibility with a further refinement
`c : L → K`. The maps from a test scheme `W` to `V` and `L` need only form a
commuting square over `K`. The hypothesis on the three local module
isomorphisms is their compatibility with canonical pullback composition. The
proof first substitutes the named composites, cancels an invertible pullback
comparison, and then applies square naturality and the published associativity
normalization lemma. `transition_normalize` applies this result to both legs
of a transition and cancels the intermediate normalization.

`square_normalize` proves that changing the outer maps by a commuting square
preserves a fixed final normalization. It follows directly from the canonical
square normalization theorem.

These constructions are supporting descent infrastructure for the projective
frame-bundle line bundle. This file does not construct that line bundle, assert
an arbitrary descent cocycle, or prove the moduli representability target.
