# Strongly regular rational points over infinite fields

Author: Worker 1531.

This module proves the published statement
`Langlands.GroupScheme.InfiniteFieldStronglyRegularPointStatement.{u}` (module
`Rational/InfiniteFieldStronglyRegularPointStatement`). Every connected
reductive group `H` over an infinite field `K` has a rational point `x` and a
closed torus `i : T ⟶ H` such that every point of `H`, on any test, that
commutes with `x` factors through `T`.

## Declaration

- `infiniteFieldStronglyRegularPoint :
  InfiniteFieldStronglyRegularPointStatement.{u}`.

## Proof

The proof is one application. It combines two published results.

1. `infiniteFieldStronglyRegularPointReduction`
   (`Rational/InfiniteFieldStronglyRegularPointReduction`) proves
   `AlgClosedStronglyRegularTorusPointStatement.{u} →
   InfiniteFieldStronglyRegularPointStatement.{u}`. It chooses a maximal
   `K`-torus `T`, which stays maximal over `K̄ = AlgebraicClosure K`. It then
   uses density of the `K`-points of `T` to pick a `K`-point in the strongly
   regular open set of `T_K̄`. Finally, it descends the factorization of each
   commuting point along the faithfully flat extension `K̄ / K`.
2. `algClosedStronglyRegularTorusPoint`
   (`Absolute/StronglyRegularTorusPointProof`) proves
   `AlgClosedStronglyRegularTorusPointStatement.{u}`. For a maximal torus `T`
   of a connected reductive group over an algebraically closed field, it
   gives a nonempty open subset of `T` such that the all-test centralizer of
   every rational point in it is contained in `T`.

The module adds no helper results.

## Literature

The statement is the rational form of the existence of strongly regular
elements that Steinberg uses in *Regular elements of semi-simple algebraic
groups* (1965), §10 (printed p.78, PDF p.31). Steinberg obtains the element
from 2.15 and density of rational points in the whole group. This route
differs: the reduction works inside a maximal `K`-torus and needs density of
rational points only for that torus. The two imported modules' Markdown files
describe the remaining steps and their sources.
