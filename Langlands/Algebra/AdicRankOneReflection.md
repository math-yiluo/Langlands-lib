# Rank one reflected from all adic quotients

This internal lemma supports the rank-one specialization of coherent formal
existence. It does not construct a coherent algebraization.

For a finite module `M` over a noetherian local commutative ring `A`, let `J`
be any proper ideal. Suppose that for every natural number `n`, the actual
module quotient `M / J^(n+1) M` is isomorphic as an `A`-module to
`A / J^(n+1)`. Then `M` is isomorphic to `A` as an `A`-module. The quotient
isomorphisms need no compatibility for this local conclusion.

The theorem
`Langlands.Algebra.AdicRankOne.nonempty_linearEquiv_of_adicQuotients`
proves this existence result. The definition
`Langlands.Algebra.AdicRankOne.equivOfAdicQuotients` chooses an actual linear
equivalence from it. The choice has no asserted normalization or functoriality.
The ring and module have independent universes, and neither completeness of
the ring nor compatibility of the quotient frames is assumed.

The implemented argument lifts a generator of the zeroth quotient. Nakayama's
lemma makes the resulting map `A → M` surjective. At each later quotient the
induced map is a surjection between isomorphic noetherian modules; Orzech's
injectivity theorem makes it injective. Hence the original map's kernel lies
in every power of `J`. Krull intersection makes this kernel zero.

This is a derived elementary local-algebra argument for the additional
rank-one step left after the coherent existence theorem in Stacks Project
Proposition 30.25.4 (Tag 088C). The registered original source
`stacks-formal-line-bundle-effectivity-2026-11-03` supplies that context,
not this particular Lean implementation. The proof invokes Mathlib's
proved Nakayama, noetherian-module injectivity and Krull intersection results.
