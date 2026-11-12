# Proof: the relative Tits system of a connected reductive group

Author: Worker 3856.

This module proves the published statement
`Langlands.GroupScheme.RelativeTitsSystemStatement` of
[`RelativeTitsSystemStatement`](RelativeTitsSystemStatement.md) at an arbitrary universe `u`,
as the theorem `Langlands.GroupScheme.relativeTitsSystem`. The statement, its three parts and
its sources (Borel–Tits 5.3, 5.15, 5.16 and 5.18; Renard V.4.1) are described in the
statement's Markdown. The statement is used unchanged: every field `k`, every connected
reductive `G`, every maximal split torus `i` and every generic cocharacter `ν`. Rank zero and
nonreduced relative root systems are included. No hypothesis is added.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Implemented proof

The proof is one application of a published implication to two proved statements:

```
relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization
  rationalBruhat rootRankOneFactorization
```

- `relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization` (module
  [`RelativeTitsGeometricReduction`](RelativeTitsGeometricReduction.md)) derives
  `RelativeTitsSystemStatement.{u}` from `RationalBruhatStatement.{u}` and
  `RootRankOneFactorizationStatement.{u}`.
- `rationalBruhat` (module [`RationalBruhatProof`](RationalBruhatProof.md), Worker 3784) proves
  `RationalBruhatStatement.{u}`: every rational point lies in a double coset `P(k) n P(k)` of
  the dynamic parabolic `P = P_G(ν ≫ i)` with `n ∈ N(k)`, and the double cosets are indexed
  disjointly by `relativeWeylGroup i = N(k)/Z(k)`.
- `rootRankOneFactorization` (module
  [`RootRankOneFactorizationProof`](RootRankOneFactorizationProof.md)) proves
  `RootRankOneFactorizationStatement.{u}`: for every relative root `a` and nonidentity rational
  point `u` of the root subgroup `U_a`, there is a unique opposite factor pair `(u′, u′′)` in
  `U_{-a}(k)` with `u′ u u′′ ∈ N(k)`, and its class is a relative reflection in `a`.

## What the applied implication does

The implication is published; it is summarized here so that the route can be followed.

1. `relativeRootSystemStatement_of_rootRankOneFactorizationStatement` turns the rank-one
   factorization into the relative root system, including faithfulness of the action of
   `N(k)/Z(k)` on the relative root span.
2. Together, the rank-one statement and the root system form
   `RootGeneratedCentralizerStructuralPremises`. Its published theorems `relativeWeylCoxeter`
   and `dynamicRootOrderedProduct` give `RelativeWeylCoxeterStatement` (the relative Weyl group
   is finite and carries a Coxeter system labelled by the simple relative roots that realizes
   the root action) and `RelativeRoot.DynamicRootOrderedProductStatement` (for every ordering
   of the indivisible positive roots, the ordered multiplication of the root subgroups is an
   isomorphism onto a representative of the dynamic unipotent subgroup).
3. `relativeTitsSystemStatement_of_coreStatements` (module
   [`RelativeTitsCoreAssembly`](RelativeTitsCoreAssembly.md)) assembles the Tits system. Its
   inputs are the two statements of step 2, `rationalBruhat`, `rootRankOneFactorization`, the
   root system of step 1, and the published unconditional proofs
   `standardParabolicEndpoints` (which identifies `standardParabolicPoints i ν ∅` with the
   rational points of the dynamic parabolic for generic `ν`) and `genericCentralizer` (the
   dynamic centralizer of a generic `ν` is the centralizer of the torus). Nondegeneracy
   `n B n⁻¹ ⊄ B` comes from actual nonidentity simple-root points
   (`RelativeSimpleRootPointData.ofActual`). The conclusion contains all three parts of
   `HasRelativeTitsSystem i ν`: the Tits axioms, the existence and uniqueness of the reflection
   of each simple root, and the injectivity of the indexing of reflections by simple roots.

## Provenance

This is internal derived content: the composition of the published reduction with the two
proofs above. It makes no new source claim. The route of the composed results differs from
Borel–Tits: the Bruhat covering is proved by orbit limits in the proper quotient `G/P`, and the
rank-one input is proved inside the identity component of a character-kernel centralizer;
see the Markdown of the cited modules.
