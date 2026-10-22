# Infinite-subgroup-finite adelic functions

For an actual number field `K : Type u`, any natural rank `n`, and an explicitly
specified subgroup `U` of `InfiniteAdelicGL K n`, this module constructs finite
vectors inside the existing continuous complex-valued, rational-left-invariant
functions on the full adelic matrix group. The ambient function space is not
assumed finite dimensional. No compactness or maximal compactness of `U` is
assumed.

`infiniteSubgroupRightAction` restricts actual right translation along the
subgroup inclusion and `AdelicGL.ofInfinite`. Its orbit span and finite-vector
predicate agree definitionally with the existing `infiniteOrbitSpan` and
`IsInfiniteFinite`. The two compatibility lemmas record these agreements.
`infiniteFiniteSubrepresentation` reuses the generic finite-vector construction,
and `InfiniteFiniteRationalFunctions` is its actual subspace.
`infiniteFiniteRightAction` restricts right translation to this subspace.

The finite and infinite adelic factors commute: `ofFinite_commute_ofInfinite`
proves this using the actual product decomposition and its multiplication law.
Consequently `finiteTranslateIntertwiner` is the actual finite right translation
as an intertwiner of the infinite subgroup action. The generic finite-vector
map lemma proves preservation of `IsInfiniteFinite`. Applying the inverse
finite translation proves the reverse implication as well.

`infiniteFiniteFiniteSubrepresentation` has exactly the same underlying
submodule, now invariant under the finite adelic group.
`infiniteFiniteFiniteRightAction` constructs its representation. The two
restricted actions commute; this is proved by the intertwiner identity and
injectivity of the subtype inclusion. `infiniteFiniteFiniteInclusion` is the
injective equivariant realization in ambient continuous functions. The
evaluation lemmas retain the convention `R(g)f(x) = f(x*g)` for both actions.

`infiniteFiniteIntersection` intersects finiteness with any specified full
adelic subrepresentation of the ambient function space. Its membership
criterion is exactly membership in that subrepresentation together with
`IsInfiniteFinite`, and the finite adelic group preserves both conditions.
The two specializations use the existing slice-wise smooth space and the
real-smooth space with a common open finite stabilizer. The latter embeds in
the former by the already proved implication from an open stabilizer to local
constancy. The generic intersection also applies to the existing central
character subrepresentations without changing their character convention.

## Sources and implemented scope

This is derived construction infrastructure for A. Borel and H. Jacquet,
*Automorphic forms and automorphic representations*, Corvallis Part I (1979):

- Section 1.5(1), printed p.190, one-based PDF p.185, defines right compact
  finiteness by the finite-dimensional span of right translates.
- Sections 3.2 and 4.1, printed p.194, PDF p.189, specify right translation,
  the infinite/finite direct product, and slice-wise smoothness.
- Section 4.7, printed p.197, PDF p.192, discusses the finite adelic action
  while keeping the infinite-type condition fixed.

The registered source is `borel-jacquet-1979-automorphic`, retained at
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The algebraic subgroup generalization and all closure, commutation and
restriction arguments are derived here. They use the actual adelic splitting
and generic finite-vector constructions, without averaging or complete
reducibility.

This does not construct a maximal compact subgroup, impose finiteness under
the enveloping-algebra center, growth or cuspidality, or prove admissibility.
No invariance under arbitrary infinite adelic translations is asserted.
These spaces remain prerequisites of the automorphic space.
