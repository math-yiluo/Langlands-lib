# Embeddings along arbitrary henselian normed extensions

Authors: Worker 114 and Worker 157 (adaptation of the published finite-extension
chart proof).

This derived construction gives the canonical homeomorphism onto the image of
`X(K) → X_L(L)` when `K` and `L` are nontrivially normed fields in universe `u`,
`L` is a normed `K`-algebra, both fields satisfy `IsHenselianValuedField`, and `X`
is a separated, quasi-separated algebraic space locally of finite type over `K`.
The topologies are `etaleChartTopology K X` and `etaleChartTopology L X_L`.
There is no restriction on the degree or transcendence degree of `L/K`.

The underlying map is `extensionPointMap L X`, which views a rational point as
an `L`-valued point and then uses `baseChangeRingPointsEquiv` to regard it as a
rational point of the actual base change. `henselianExtensionPointHomeomorphRange`
is the homeomorphism to its range obtained from the proved embedding by
`IsEmbedding.toHomeomorph`.

## Implemented proof

The module adapts the published `HenselianFiniteExtensionPointEmbeddingProof`
of Worker 157, rather than asserting a new result from the literature.

1. `NormedExtensionEmbedding.exists_invariant_open` constructs arbitrarily small
   open neighborhoods of a rational affine point inside `AlgPoint K A L`. The
   evaluation topology supplies finitely many coordinate balls centered at its
   coordinates in `K`. Each ball is invariant under every isometric
   `K`-automorphism of `L`. The commutative `K`-algebra `A` need not be finite type
   for this helper.
2. `exists_desc_of_galois_invariant` descends an affine point fixed by all
   automorphisms of an arbitrary Galois extension. It applies Mathlib's
   `InfiniteGalois.mem_range_algebraMap_iff_fixed` coordinate by coordinate and
   uses injectivity of the field embedding to verify the algebra-map laws.
3. `isEmbedding_of_isGalois` uses affine finite-type etale charts through rational
   points, their open point maps over the henselian target, and local injectivity
   from separatedness. Inside a locally injective chart neighborhood it takes an
   invariant coordinate neighborhood. A lift over a rational space point and all
   its conjugates remain in that neighborhood and have the same image; injectivity
   makes them equal. Galois descent then produces a rational chart point. This
   proves that the continuous injective extension map induces the source topology.
   The Galois extension may have infinite degree; `K` and `L` are both henselian.
4. `isEmbedding_of_isSeparable` treats a separable algebraic extension `L/K` by
   embedding it in `SeparableClosure K`. Henselianity supplies the extending norm
   on that closure and makes the lift isometric. The embedding for the Galois
   closure, continuity of the intervening map, and `IsEmbedding.of_comp` give the
   result for `L/K`. Henselianity of `L` is not an additional premise of this helper.
5. `isEmbedding_henselianExtensionPointMap` factors an arbitrary extension through
   `S = separableClosure K L`. The first arrow is the separable algebraic case.
   The second uses the published relatively separably closed extension result,
   since `separableClosure S L = bottom`. The actual base-change tower isomorphism
   identifies the composition with `extensionPointMap L X`.

## Scope

This is supporting construction for `HenselianExtensionPointEmbeddingStatement`.
It proves the embedding and constructs its homeomorphism onto the range for
separated spaces. The conditional closed-image conclusion and the passage to
spaces covered by separated open subspaces remain to be proved. This module does
not claim the whole target.
