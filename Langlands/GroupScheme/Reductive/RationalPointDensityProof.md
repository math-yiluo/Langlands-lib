# Zariski density of rational points of connected reductive groups (proof)

This module proves `Langlands.GroupScheme.ReductiveRationalPointDensityStatement`:
for every infinite field `k : Type u` and every connected reductive group scheme
`G` over `Spec k`, the union of the images of the `k`-rational points of `G` is
dense in the Zariski topology of `G.X`.

## Conditional assembly

`Langlands.GroupScheme.reductiveRationalPointDensity_of_domination_of_splitting`
derives the statement from two published propositions:

- `ReductiveTorusDominationStatement`: over an infinite field, every connected
  reductive `G` admits a torus `T` over `k` and a morphism `f : T.X ⟶ G.X` over
  `Spec k` with dense image. `f` need not be a group homomorphism.
- `TorusFiniteGaloisSplittingStatement`: every torus `T` over a field `k`
  splits over some finite Galois extension `K / k`.

The proof follows these steps.

1. Torus domination gives `T`, `f` and the density of the image of `f.left`.
2. Finite Galois splitting applied to `T` gives a finite Galois extension
   `K / k` such that the base change of `T` to `K` is a split torus.
3. The Library theorem
   `Langlands.GroupScheme.TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange`
   (module `Langlands.GroupScheme.Torus.RationalDensity`) shows that the
   `k`-rational points of `T` are dense, because `k` is infinite and `T`
   splits over the finite Galois extension `K`.
4. The Library lemma
   `Langlands.AlgebraicGeometry.PointTopology.hasDenseRationalPoints_of_denseRange`
   carries dense rational points along a morphism over `Spec k` with dense
   image. Composing a rational point of `T` with `f` gives a rational point of
   `G`, and the image of a dense set under a continuous map with dense range is
   dense. Applied to `f`, this gives the statement for `G`.

The conditional theorem takes both propositions as explicit hypotheses and
adds no other assumption. Like the statement, it is stated at an arbitrary
universe `u`.

## Discharging the splitting hypothesis

`Langlands.GroupScheme.reductiveRationalPointDensity_of_domination` removes the
splitting hypothesis. It applies the conditional theorem to the published
proof `Langlands.GroupScheme.torusFiniteGaloisSplitting` (module
`Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof`). Its only remaining
hypothesis is `ReductiveTorusDominationStatement`.

## The final theorem

`Langlands.GroupScheme.reductiveRationalPointDensity` proves
`ReductiveRationalPointDensityStatement.{u}` with no hypotheses. It applies
`reductiveRationalPointDensity_of_domination` to the published proof
`Langlands.GroupScheme.reductiveTorusDomination` (module
`Langlands.GroupScheme.Reductive.TorusDominationProof`) of
`ReductiveTorusDominationStatement`. That proof starts from finitely many
closed subtori that generate `G` and takes as dominating torus a finite power
of their product. The present module uses only its conclusion.

## Relation to the literature

Milne, *Algebraic Groups* (2017), Theorem 17.93(b) (printed page 382) derives
the density from the unirationality of reductive groups. The Lean proof
follows a different route: it uses only a dominant morphism from a torus
together with the density of rational points on tori. That density is a form
of Milne's Corollary 12.65 (printed page 251), proved in the Library module
named in step 3.
