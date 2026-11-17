# Equivariant projections from a finite quotient average

Let `ρ` and `σ` be representations of an abstract group `G` over a commutative
ring, and let `N` be a normal subgroup. Assume `G/N` is finite and its order is
invertible in the coefficient ring. The construction `intertwinerAverage`
turns an `N`-equivariant linear map into a `G`-equivariant linear map by averaging
its conjugates over the quotient.

The formula `intertwinerAverage_apply` holds for every choice of coset
representatives. The lemma `intertwinerAverage_leftInverse` proves that averaging
preserves a left inverse of a `G`-equivariant map. The lemma
`intertwinerAverage_isProj` proves that an `N`-equivariant projection onto a
`G`-stable submodule averages to a `G`-equivariant projection onto that same
submodule. No field or finite-dimensional hypothesis is needed.

The implementation applies `normalQuotientAverage` to the representation on
linear maps, with action `g · p = σ(g) ∘ p ∘ ρ(g⁻¹)`. Its invariants are exactly
the equivariant linear maps. For a retraction, every conjugate remains a
retraction. For a projection, stability preserves the image condition, while
each conjugate fixes every vector of the submodule. The normalized sum therefore
has both projection properties.

This is derived infrastructure for the averaging step of Nagata's theorem.
The source motivation is J. S. Milne, *Algebraic Groups*, corrected reprint (2022),
Exercise 4-3, printed p.97, and the proof of Corollary 22.43, printed p.479.
The latter passage assumes characteristic zero; this abstraction instead states
the exact invertibility hypothesis used by the averaging argument. The official
errata snapshot of 4 November 2026 has no correction to these passages. Group
scheme components, scalar descent, and equivariance on all affine test algebras
are separate obligations.
