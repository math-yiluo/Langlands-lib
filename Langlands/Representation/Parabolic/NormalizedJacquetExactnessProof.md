# Exactness of the actual normalized block Jacquet maps

Authors: Worker 23 and Worker 187.

`Langlands.Parabolic.normalizedJacquetExactness F T B U V W` proves exactly
the published `Langlands.Parabolic.NormalizedJacquetExactnessClause F T B U V W`
from `Parabolic/NormalizedJacquetStatement`. The parameters are every prime
`p`, every `F : PadicField.{uF} p`, every compatible `T : F.TopologicalData`,
every natural rank `n` (rank zero included), every block shape `B`, and three
complex carrier modules `U`, `V`, `W` with independent universes. All
topologies come from `T.topology`. No admissibility, finite length,
finite-dimensionality or compact-exhaustion premise is added. The statement
pair and everything it imports are unchanged.

Write `P = B.parabolic F.Carrier` and `N = B.unipotentRadical F.Carrier`.

## Implemented proof

The clause concerns the maps
`iN = twistIntertwining χ (leviCoinvariantsMap B (Jacquet.restrictMap i P))`
and the analogous `qN`, where `χ` is the inverse half-character of
`T.leviModulus B`. Neither `twistIntertwining` nor `leviCoinvariantsMap`
changes the underlying linear map. That map is, by definition, Mathlib's
`Representation.Coinvariants.map` of the restriction of `i` to `N` (the
restriction of `i` to `P`, then to `N`). So the clause holds definitionally
once Mathlib's coinvariant maps for the actual radical are exact. The
twisting character and the Levi action play no part in the argument.

1. `isSmooth_radical` restricts a smooth `GL_n(F)` action to `P` and then to
   `N` with the published `isSmooth_comp`. Subgroup inclusions are continuous
   for the subspace topologies.
2. `radicalCoinvariants_exact` proves injectivity, range = kernel and
   surjectivity of these coinvariant maps. It needs only the middle
   representation `σ` to be smooth.
   - Injectivity is `coinvariants_map_injective_of_smooth` from
     `Jacquet.ExactProof`, applied to the topological group `N`. Its
     finite-containment hypothesis, that every finite subset of `N` lies in a
     compact open subgroup of `N`, is the published
     `unipotentFiniteContainment F T B` for this actual radical. The
     topological-group instance on `N` comes from
     `T.generalLinearTopologicalGroup n` through Mathlib's subgroup instances.
   - Range = kernel is the algebraic `coinvariants_map_range_eq_ker`, applied
     to the restricted maps. Restriction does not change the underlying
     linear maps, so the hypothesis `range i = ker q` and surjectivity of `q`
     carry over unchanged.
   - Surjectivity is the algebraic `coinvariants_map_surjective`.
3. `normalizedJacquetExactness` introduces the clause's data and the two let
   bindings `iN` and `qN`, then closes the goal with step 2. Smoothness of the
   outer representations is part of the hypotheses but is not used.

## Consumer theorems for the Jacquet functor

In namespace `Langlands.PadicField.TopologicalData`, for the actual
`T.normalizedJacquetMap` and `T.normalizedJacquetFunctor` of
`Jacquet/Parabolic`:

- `normalizedJacquetMap_toLinearMap` (proved by `rfl`): the underlying
  linear map of `T.normalizedJacquetMap B f` equals that of the clause's
  normalized quotient intertwiner built from `f`.
- `normalizedJacquetMap_toLinearMap_eq_coinvariantsMap` (proved by `rfl`):
  both equal Mathlib's coinvariant map of the restriction of `f` to `N`.
- `normalizedJacquetMap_exact`: for intertwiners `i : ρ → σ` and
  `q : σ → τ` with `σ` smooth, `i` injective, `q` surjective and
  `range i = ker q`, the maps `T.normalizedJacquetMap B i` and
  `T.normalizedJacquetMap B q` are injective, exact in the middle, and
  surjective. The published `isSmooth_of_injective` and
  `isSmooth_of_surjective` give smoothness of `ρ` and `τ`. The theorem then
  applies `normalizedJacquetExactness` itself, so this is the same exactness
  result.
- `normalizedJacquetFunctor_map_hom` (proved by `rfl`): the actual functor's
  image of a morphism has exactly the intertwiner `T.normalizedJacquetMap`
  of its underlying intertwiner.
- `normalizedJacquetFunctor_map_exact`: for morphisms `i : A₁ ⟶ A₂`,
  `q : A₂ ⟶ A₃` in `SmoothRep ℂ GL_n(F)` (topology `T.generalLinearTopology n`)
  whose underlying intertwiners satisfy the same three conditions, the
  underlying intertwiners of `(T.normalizedJacquetFunctor B).map i` and
  `.map q` satisfy the three conclusions. The functor's maps are
  `T.normalizedJacquetMap` of the underlying intertwiners by definition, and
  `A₂` is smooth because it is an object of `SmoothRep`. These are statements
  about underlying intertwiners; no abelian-category structure on `SmoothRep`
  is used or claimed.

## Sources and scope

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, revision April 29, 2019 (`casselman-2019-jacquet-module`), PDF
pp.3-4. Lemma III.3.1 states that a p-adic unipotent group "possesses
arbitrarily large compact open subgroups". Proposition III.3.4 states that
for an exact sequence `0 → U → V → W → 0` of smooth representations of `N`,
`0 → U_N → V_N → W_N → 0` is exact. Right exactness follows from the
definition of `V(N)`, and injectivity uses compact open subgroups and
averaging. Worker 23 re-read both pages for this proof. The Lean route
follows the source: the finite containment for the actual block radical
(the role of III.3.1) is the published `unipotentFiniteContainment`, and the
generic smooth coinvariant argument (III.3.4) is Worker 200's
`Jacquet.ExactProof`. The statement's further locators, Bernstein-Zelevinsky
1977 §§1.8-1.9 and §2.3, are listed in `NormalizedJacquetStatement.md`.

The result is the exactness clause only. The smoothness, admissibility and
Frobenius clauses of `NormalizedJacquetStatement` are not proved here.

## Dependencies

The imports are the unchanged published `Parabolic.NormalizedJacquetStatement`,
`Parabolic.UnipotentFiniteContainment`, `Jacquet.ExactProof`,
`Smooth.Transfer.PullbackProof` and `Jacquet.Parabolic`. All reused results
are referenced by Lean name. Worker 23 wrote the core proof and the stronger consumer exactness consequences.
Worker 187 independently compiled the consumer identifications and exactness
transfer, then supplied the named functor-map identification in this combined pair.
