# Subrepresentations from scalar central subrepresentations

Module `Langlands.Representation.ScalarSubReduction`. These are internal,
purely algebraic results over an arbitrary field `R` and group `G`. They contain
no analytic assertion and no analytic projector. They are dual to the existing
`Langlands.quotientOfScalarCentralQuotients` (`Langlands.Representation.ScalarQuotientReduction`)
and `Langlands.quotientOfIsotypicRange` (`Langlands.Representation.IsotypicQuotient`):
those results produce an irreducible *quotient*; these produce an irreducible
*subrepresentation* from a given irreducible quotient.

## Declarations

- `ScalarSubReduction.inclusion ρ S`: the inclusion `S → ρ` of a
  subrepresentation, as an intertwiner. `inclusion_injective` records its
  injectivity.
- `ScalarSubReduction.centralDefect ρ z c`: for a central element `z` and a
  scalar `c`, the self-intertwiner `ρ(z) - c`. `ρ(z)` commutes with every
  `ρ(g)` because `z` is central. `centralDefect_apply` gives the formula.
- `ScalarSubReduction.centralDefect_not_injective`: let `ρ` have finite length
  as a `MonoidAlgebra R G`-module, and let `q : ρ → σ` be a surjective
  intertwiner onto an irreducible `σ` on which `z` acts by `c`. Then `ρ(z) - c`
  is not injective. Proof: a finite-length module is Artinian, and an injective
  endomorphism of an Artinian module is surjective
  (`IsArtinian.surjective_of_injective_endomorphism`). But `q ∘ (ρ(z) - c) = 0`,
  so if the defect were surjective then `q` would vanish. That is impossible,
  since `q` is surjective and `σ` is nonzero.
- `ScalarSubReduction.exists_injective_of_isotypicProjector`: let `σ` be
  irreducible and `P` an idempotent self-intertwiner of `ρ`. Suppose the range
  of `P` is the supremum of the ranges of all intertwiners `σ → ρ`, and no
  subrepresentation of `ker P` surjects onto `σ`. Then any surjection `q : ρ → σ`
  gives an injective intertwiner `σ → ρ`. Proof: `q` restricted to `ker P` is
  zero, because by irreducibility it is either surjective or zero, and the
  first case is excluded by the hypothesis applied to `⊤`. Then `q v = q (P v)`,
  because `v - P v ∈ ker P`. If every intertwiner `σ → ρ` were zero, the range of
  `P` would be `⊥` and `q` would be zero. So some intertwiner `σ → ρ` is
  nonzero, and it is injective by irreducibility of `σ`.
- `Langlands.exists_injective_of_scalarCentralSubs` (the public reduction): let
  `ρ` have finite length, `σ` be irreducible with `σ(z) = χ(z)` for every
  central `z`, and `q : ρ → σ` be surjective. Suppose the following holds for
  every representation `τ` with an injective intertwiner `τ → ρ` on which the
  whole center acts by `χ`: if `τ` surjects onto `σ`, then `σ` embeds in `τ`.
  Then `σ` embeds in `ρ`. The hypothesis is about *subrepresentations* only;
  the carrier universe of `τ` is that of `ρ`.

## Proof of the reduction

The private theorem `sub_exists` proves the reduction by strong induction on
the natural-number length `(repLength τ).toNat`. It ranges over all `τ` with an
injection `i : τ → ρ` and a surjection onto `σ`, starting from `τ = ρ`,
`i = id`. Every such `τ` has finite length, being a submodule of `ρ`
(`IsFiniteLength.of_injective`).

- If the whole center acts on `τ` by `χ`, apply the supplied hypothesis.
- Otherwise pick a central `z` and a vector `v` with `τ(z) v ≠ χ(z) v`. Let
  `D = τ(z) - χ(z)`, with kernel `K` and range `A`. By
  `centralDefect_not_injective`, `K ≠ 0`; since `D v ≠ 0`, `A ≠ 0`. The exact
  sequence `0 → K → τ → A → 0` gives
  `repLength τ = repLength K + repLength A` (`repLength_eq_add_of_exact`), so
  both have strictly smaller length.
  - If `q` restricted to `K` is surjective, recurse on `K` with the injection
    `τ ⊇ K → ρ`, and compose the resulting embedding with `K → τ`.
  - Otherwise `q|K = 0` by irreducibility of `σ`. Then `q` factors through
    `τ / K ≅ A`: `quotKerEquivOfSurjective` and `liftQ`, made equivariant by
    hand. This gives a surjection `A → σ`. Recurse on `A`, which is a
    subrepresentation of `τ` and hence injects into `ρ`, and compose with the
    inclusion `A → τ`.

## Provenance

This is internal derived algebra. In the proof of Silberger's Theorem 3.3.1
(printed pp. 126-127, PDF pp. 132-133 of `silberger-1979-harmonic-analysis`),
the Jacquet module is cut down to a submodule on which the center acts through
the given class, and that module is split by its semisimple coefficient
algebra. Here the reduction to exact scalar central action is done instead by
the length induction above. The splitting step is a hypothesis: the
`isotypicProjector` theorem consumes a supplied projector. No Schur lemma is
used.
