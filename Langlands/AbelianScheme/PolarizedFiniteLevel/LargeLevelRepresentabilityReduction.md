# Eventual fine representability from gluing, the sheaf property, charts and quasi-projectivity

This internal module reduces the published target
`LargeLevelRepresentabilityStatement` to four named statements. It adds no
mathematical assertion beyond that implication. The four statements stay
explicit hypotheses.

## Result

`largeLevelRepresentability_of_chartCover` is a proved definition: a `def`
whose type is the proposition `LargeLevelRepresentabilityStatement`. It takes
four hypotheses:
- `Hglue : LevelBaseOpenChartGluingStatement` (Stacks 01JJ on level bases);
- `Hsheaf : ModuliZariskiSheafStatement` (the moduli functor is a Zariski sheaf
  for `n ≥ 3`);
- `Hchart : LargeLevelChartCoverStatement` (eventual open chart covers);
- `Hqp : LargeLevelQuasiProjectivityStatement` (eventual quasi-projectivity of
  every representing level base).

## Proof

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. `Hchart` gives a bound `N₁` and
`Hqp` gives a bound `N₂`; take `N = max N₁ N₂`. For `n ≥ N` with `3 ≤ n`:
1. `Hchart` gives an open chart cover `a` of the moduli functor by level bases
   `X i`.
2. `Hsheaf` gives the Zariski sheaf property of the moduli functor.
3. `Hglue`, applied to steps 1 and 2, gives a level base `Y` and a natural
   isomorphism `e` from its functor of points to the moduli functor.
4. `Hqp`, applied to `Y` and `e`, gives quasi-compactness of the canonical
   morphism `Y.toLocalizationSpec` and an immersion `i` into a projective space
   over `ℤ[1/n]` lying over it.

The target's witnesses are then `Y`, `π = Y.toLocalizationSpec`, `m`, `i` and
`e`.

## Provenance

This is an internal derivation. It only combines the conclusions of the four
statements, which are documented in their own modules.
