# Proof of general standard-Levi conjugation and lift independence

`standardLeviConjugation` proves the published proposition
`StandardLeviConjugationStatement.{u}` exactly, at arbitrary universe `u`.
Fix any field `k`, connected reductive `G` over `k`, actual maximal split
torus `i : T.toGrp ⟶ G` and generic cocharacter `ν`, and write
`Δ = simpleRelativeRoots i ν`. The theorem gives both clauses of the target.
First, if `J, J' ⊆ Δ` and the relative Weyl class of a normalizing point `n`
maps the encoded roots of `J'` onto those of `J`, then `standardLevi i ν J'`
is the preimage of `standardLevi i ν J` under conjugation by `n`. Second, for
every `J ⊆ Δ`, two normalizing points with the same Weyl class have the same
conjugate of `standardLevi i ν J`. Both equalities hold on every test scheme.
This is the content of Renard V.4.3 (equation (V.4.3.1)) over arbitrary fields,
as specialized in the statement's Markdown.

## Implemented proof

The proof composes three published theorems; it adds no hypothesis and no new
argument.

1. `rootRankOneFactorization` (module `Rational.RootRankOneFactorizationProof`)
   proves `RootRankOneFactorizationStatement.{u}` unconditionally. For every
   relative root and nonidentity rational point of its root subgroup, it gives
   an opposite factor pair whose product normalizes the torus and represents a
   reflection.
2. `relativeRootSystemStatement_of_rootRankOneFactorizationStatement` (module
   `Rational.RootSystemFromFactorPairs`) turns this into
   `RelativeRootSystemStatement.{u}`. It uses only the existence of opposite
   factor pairs, together with the published positive-root stabilizer theorem,
   to build the actual relative root system `HasRelativeRootSystem i`.
3. `standardLeviConjugationStatement_of_relativeRootSystemStatement` (module
   `Rational.StandardLeviConjugationAssembly`) derives the target from
   `RelativeRootSystemStatement.{u}`. The root system gives finiteness of `Δ`
   and a standard cocharacter for every `J ⊆ Δ`. The encoded-root transport
   theorem `standardLevi_eq_comap_of_rootSubset_image` then gives the first
   clause. The unconditional `standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq`
   gives the second.

The universe `u`, arbitrary fields, the actual normalizer quotient and all test
schemes are preserved throughout. `Lean.collectAxioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance and credits

This is an internal composition of published Library results, imported by Lean
name. Worker 3483 pointed out this route through the published rank-one
factorization theorem. Worker 3767 checked and wrote the module.
