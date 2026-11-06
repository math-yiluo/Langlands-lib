# Rank-one centralizer generation from Kneser–Tits and root-generated rank-one generation

Author: Worker 1662.

Module `Langlands.GroupScheme.SimplyConnected.RankOneCentralizerGenerationReduction`.

## The statement

`Langlands.GroupScheme.SimplyConnectedRankOneCentralizerGenerationReductionStatement.{u}`
is the proposition

```text
RootGeneratedCentralizerRankOneStatement.{u} →
  SimplyConnectedKneserTitsCentralizerStatement.{u} →
  SimplyConnectedRankOneCentralizerGenerationStatement.{u}
```

All three propositions are published and unchanged. Write
`U_a(F)` for the carrier `(RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _))`
of the Library root group at the identity test object, `Z(F)` for
`centralizerPoints i`, `G(F)^+` for
`Subgroup.closure (⋃ a ∈ relativeRoots i, U_a(F))`, and `Z(F)^1` for
`Plancherel.rationalCommonNormKernel Z`.

- `RootGeneratedCentralizerRankOneStatement` (module
  `Rational.RootGeneratedCentralizerRankOneStatement`). For every field `k`,
  every connected reductive `G` over `k` and every maximal split torus
  `i : S ⟶ G`,
  `Z(k) ⊓ G(k)^+ ≤ closure (⋃ a ∈ relativeRoots i, Z(k) ⊓ closure (U_a(k) ∪ U_{-a}(k)))`.
- `SimplyConnectedKneserTitsCentralizerStatement` (module
  `SimplyConnected.KneserTitsCentralizerStatement`). For a simply connected
  `G` over a nonarchimedean local field `F` with maximal split torus `i` and a
  closed subgroup `j : Z ⟶ G` representing `torusCentralizer i`,
  `(rationalPoints.map j).range ≤ (Z(F) ⊓ G(F)^+) ⊔ Z(F)^1.map (rationalPoints.map j)`.
- `SimplyConnectedRankOneCentralizerGenerationStatement` (module
  `SimplyConnected.RankOneCentralizerGenerationStatement`) is the target. With
  the same data it states
  `(rationalPoints.map j).range ≤ closure (⋃ a ∈ relativeRoots i, Z(F) ⊓ closure (U_a(F) ∪ U_{-a}(F))) ⊔ Z(F)^1.map (rationalPoints.map j)`.

The theorem
`Langlands.GroupScheme.simplyConnectedRankOneCentralizerGeneration_of_kneserTits`
proves the implication for every universe `u`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`. Once the first two propositions are
proved, the target follows by applying this theorem to their proofs.

## The proof

Fix the data of the target: `F`, `G` with `[IsAffineHom G.X.hom]`, a proof
`hsc : IsSimplyConnected G`, `S`, `i`, `hi : IsMaximalSplitTorus i`, `Z`, `j`
and `hj : (torusCentralizer i).IsRepresentedBy j`.

1. The Kneser–Tits statement, applied to exactly these data, bounds the range
   of `rationalPoints.map j` by `(Z(F) ⊓ G(F)^+) ⊔ Z(F)^1.map (rationalPoints.map j)`.
2. `G` is connected reductive: `hsc.isSemisimple.isConnectedReductive`. The
   root-generated statement, applied to `F`, `G`, this proof, `S`, `i` and
   `hi`, gives `Z(F) ⊓ G(F)^+ ≤ closure (⋃ a, Z(F) ⊓ closure (U_a(F) ∪ U_{-a}(F)))`.
   Its left side is syntactically the first term of the bound in step 1.
   That statement fixes the affineness instance by `hG.isAffineHom`, while the
   target carries its own instance `[IsAffineHom G.X.hom]`. `IsAffineHom` is a
   proposition, so the two instances are definitionally equal and the two
   subgroups agree.
3. `sup_le_sup_right` turns step 2 into an inequality between the joins with
   `Z(F)^1.map (rationalPoints.map j)`, and `le_trans` composes it with
   step 1. The result is the target inequality.

## Provenance

This is an internal reduction, proved in Lean. It introduces no assertion
beyond its two published inputs. It records the split of the target into a
field-general part and a local Kneser–Tits part. Each input's Markdown gives
its own provenance: Borel–Tits, *Groupes réductifs* (1965), §5, for the
root-generated statement, and Prasad–Raghunathan's local Kneser–Tits theorem
for the Kneser–Tits statement.
