# Néron models from weak Néron models and birational group laws

The module `Langlands.AbelianScheme.NeronModelExistenceReduction` states and proves that
three results together give Néron models of abelian varieties over discrete valuation
rings: the existence of weak Néron models, the existence of solutions of birational
group laws, and the construction of the birational group law on a suitable model.

## `NeronModelExistenceReductionStatement`

The proposition is the implication

`WeakNeronModelExistenceStatement.{u} → BirationalGroupLawSolutionStatement.{u} →
NeronModelOfWeakNeronModelStatement.{u} → NeronModelExistenceStatement.{u}`

between the following Library statements:

- `Langlands.AbelianScheme.WeakNeronModelExistenceStatement`: every abelian variety `B`
  over the fraction field `K` of a discrete valuation ring `V` has a smooth, separated
  `V`-model of finite type with the weak Néron mapping property.
- `Langlands.AlgebraicGeometry.BirationalGroupLawSolutionStatement`: over a discrete
  valuation ring, every birational group law on a smooth, separated, faithfully flat
  scheme of finite type has a solution. If the law is defined on the whole generic fibre
  and both universal translations map onto it there, the solution can be chosen with
  domain the whole scheme.
- `Langlands.AbelianScheme.NeronModelOfWeakNeronModelStatement`: from a weak Néron model
  of `B`, one obtains a smooth, separated, faithfully flat model `X` of `B` of finite type
  with a birational group law of that kind. Every solution whose domain is all of `X` has
  the Néron mapping property `NeronModelInfra.NeronModelPropertyBundle`.
- `Langlands.AbelianScheme.NeronModelExistenceStatement`: every abelian variety over the
  fraction field of a discrete valuation ring has a Néron model
  (`Langlands.AbelianScheme.NeronModel`).

## Source and provenance

Bosch, Lütkebohmert and Raynaud, *Néron Models* (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`), §1.3, Corollary 2 and its proof (printed
pp. 16–18), and §4.4, Corollary 4 (printed pp. 110–111). The Néron model is the
`R`-group scheme solving the birational group law on the model built from a weak Néron
model. The implication is derived from this argument, cut along the three Library
statements above.

## Declarations and proofs as implemented

- `solution_genericIso`: let `X` be a `V`-model of `B` (an isomorphism `eX` of `B` with
  the generic fibre of `X`), `m` a birational group law on `X`, and `σ` a solution of `m`
  with `σ.domain = ⊤`. Then `B` is isomorphic over `K` to the generic fibre of the
  solution group scheme `G`. Proof: since the domain of `σ` is all of `X`, the embedding
  of `σ` gives an open immersion `j : X ⟶ G` over `V`. Its generic fibre `j_K` is an open
  immersion (base change), and it is proper because the generic fibre of `X` is the proper
  scheme `B` and the generic fibre of `G` is separated. The image of `j_K` is therefore
  closed. It contains a generization of every point of the generic fibre of `G`, because
  the image of `σ`'s embedding meets every fibre densely
  (`BirationalGroupLaw.Solution.embedding_dense`). So `j_K` is surjective, hence an
  isomorphism.
- `neronModelExistenceReduction` proves the proposition. Apply the weak Néron model
  statement to `B`, then `NeronModelOfWeakNeronModelStatement` to the weak Néron model,
  which gives `X`, `eX` and `m`. The full-domain clause of
  `BirationalGroupLawSolutionStatement` gives a solution `σ` with `σ.domain = ⊤`. By
  `NeronModelOfWeakNeronModelStatement`, `σ` has the Néron mapping property, and
  `solution_genericIso` identifies its generic fibre with `B`.
  `Langlands.AbelianScheme.NeronModel.ofScheme` then turns the group scheme of `σ` into a
  Néron model of `B`.
