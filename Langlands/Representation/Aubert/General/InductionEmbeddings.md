# Embeddings under actual normalized induction across carrier universes

This internal construction specializes the published
`Langlands.Induction.smoothInducedMap` and
`Langlands.Induction.smoothInducedMap_injective` to the actual full-parabolic
normalized induction functor. It supplies an embedding and finite-length
descent interface for coefficient representations with independent carrier
universes. No external representation-theoretic assertion is used.

Let `G : Type uG` be a locally compact nonarchimedean group, let `P`, `M`
and `U` be subgroups, and suppose `h : IsSemidirectDecomposition P M U`.
Assume that `U` is closed. The coefficient representations `A` and `B`
are smooth complex representations of the literal subgroup `M`, with
carriers in independent universes `uV` and `uW`.

`normalizedInductionMap h hU f` takes an actual intertwiner from `A` to
`B`. It inflates this intertwiner along `h.projection : P →* M`, twists
both actions by the same full-parabolic Haar half character
`HaarModulus.closedHalfCharacter U hU P h.le_normalizer`, and applies
smooth induction. Thus its source and target are exactly the representations
underlying the published normalized functor objects, with output carriers in
`max uG uV` and `max uG uW`. It introduces no Levi-factorization
assumption on that character.

`normalizedInductionMap_eval` states that the resulting map sends a function
`v` to the function `g ↦ f (v g)`. Its intertwining and smoothness properties
are those of the published smooth induced map. When the two coefficient
universes coincide, `normalizedInductionMap_hom` identifies this map
definitionally with the published categorical functor's action on morphisms.

`normalizedInductionMap_injective` applies the published injectivity theorem.
Inflation and twisting preserve the underlying coefficient linear map, so
the given injectivity of `f` is precisely its required hypothesis. The
pointwise formula also explains this conclusion: equality of the images
gives equality at every argument after applying the injective map `f`.

`normalizedInduction_hasFiniteLength_of_injective` converts that actual
induced intertwiner into a linear map over the acting group algebra using
`Representation.IntertwiningMap.equivLinearMapAsModule`. It then applies
`IsFiniteLength.of_injective`. Finite length is composition length over
the actual group algebra `ℂ[G]`; the theorem assumes that the induced
target has finite length and proves it for the induced source. It does
not assert that either induction has finite length without this hypothesis.

The construction is useful at a carrier-universe boundary in the
Renard VI.6.2 proof: an embedding can be obtained using a larger
representation universe, while the desired induction retains the original
carrier universe. The module proves only the indicated map and descent
facts. It supplies neither the cuspidal embedding, finite length of
supercuspidal induction, transitivity, nor the structural realization of
the source parabolics.
