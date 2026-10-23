# Naturality of the multiplicative Tate comparison in the test scheme

For any scheme `S`, predicate `P : ℕ → Prop`, and morphism
`a : T' ⟶ T` in `Over S`, the published Gm-to-roots comparison commutes
with test-scheme restriction. The declarations are in
`Langlands.GroupScheme.Gm.TateComparison`.

## Internal provenance

`TestScheme` constructs restriction of actual torsion sections and their
Tate limits. The published `MultiplicativeDivisibility` module constructs
`integralEquiv` and `awayEquiv` from actual Gm torsion to roots of unity in
the global-section ring. Its imported finite-level comparison has the
naturality law `levelEquiv_restrict`. This module assembles that law
coordinatewise. No roots, bases or trivializations are chosen, and no new
claim is attributed to original literature.

## Commuting squares

`integralEquiv_testRestrict` states, for every selected actual Gm Tate
element `x`,

```text
integralEquiv T' P (Tate.testRestrict (Gm S).toGrp P a x) =
  TateTwist.Divisibility.map P a.left.appTop.hom (integralEquiv T P x).
```

Here `a.left.appTop.hom` maps the global-section ring of `T` to that of
`T'`. The root-limit map applies this ring map to each root of unity.
The equality follows by extensionality of coherent families and the
finite-level naturality theorem. Taking `P` constantly true gives the full
integral Tate comparison.

`integralEquiv_symm_testRestrict` is the inverse square. It is proved by
applying the injective target comparison and simplifying with the forward
square and the inverse identities.

For every natural modulus `m`, `awayEquiv_testRestrict` and
`awayEquiv_symm_testRestrict` state the same two squares using the existing
away scalar bundles: `Tate.awayTestRestrict` on Gm points and
`TateTwist.Divisibility.awayLinearMap` on roots. They specialize the selected
laws to the predicate `Nat.Coprime · m`; primality is not required.

## Scope

The maps use the existing integral topologies and residue actions. The
new assertions are pointwise naturality equalities, with continuity of
restriction supplied by `TestScheme` and continuity of the comparisons
supplied by `MultiplicativeDivisibility`. Changing the base scheme,
geometric path transport, rationalization and Weil pairings remain
separate constructions.
