# Normal-basis and principal-unit correction product comparison

This proposition states that the finite products of a normal-basis correction sequence agree with the usual principal-unit correction products after expressing each term as a sufficiently deep principal unit. It supplies the exact source target, with no proof of the comparison.

## Pinned source and name map

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`, M150.012, statement lines 277–287 and proof lines 288–293. The file SHA-256 is `2712c4da08b98e9fbdb071e3c57281fc5e33d3f5fcf6b44c8e85fda77c8a9fa2`.

The [readable pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean>) is registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_eq_principalUnitsCorrectionProduct` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_eq_principalUnitsCorrectionProductStatement` |

## Complete telescope and mathematical content

The definition explicitly retains the section telescope from source lines 30–34, in order:

```lean
(K L : Type u)
[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
```

Both fields share universe `u`; the types are explicit and the instances remain instance binders. There is no `omit` applying to M150.012, and the explicit telescope preserves all these source hypotheses. No topology on `L` or integral-closure hypothesis is added.

Its remaining binders are exactly:

```lean
{b n : Nat}
(hb : chosenBaseUniformizerPowSubmodule K L b
    (chosenNormalBasisIntegerLattice K L) ≤
  integerRingFieldSubmodule K L)
(hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
(hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
(d : Nat)
```

Here `hb` puts the lattice dilate at level `b` in the extension integer ring, `hbn` bounds the starting level, and `hz` puts the `i`-th correction in the normal-basis set at level `n+i`. The already published `chosenNormalBasisPrincipalUnitSequenceAsPrincipalUnits K L hb hbn z hz` constructs an actual element of `principalUnits L (1+i)` at each index `i`, using the actual published lattice-bound proof.

The left side of the target is the product of the first `d` terms of `z`, formed by the published `chosenNormalBasisPrincipalUnitCorrectionProduct`. The right side is `principalUnitsCorrectionProduct L 1` applied to that published subtype-valued sequence, at the same index `d`. Equality is in `𝒪[L]ˣ`, including the empty product case.

## Dependencies and modifications

The two normal-basis data definitions are imported from `NormalBasisInfiniteProduct.PrincipalUnitSequence` and `.CorrectionProduct`. The ordinary correction product is imported from `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.CorrectionDefinitions`, where it is named `Langlands.NYLL.LocalFieldTheory.principalUnitsCorrectionProduct`. No data definition is duplicated, and the subtype's membership proof is the actual published proof imported by `PrincipalUnitSequence`.

Worker 197 split out M150.012, prefixed the namespace with `Langlands.NYLL`, appended `Statement`, changed the theorem into a `Prop`-valued `def`, made the section telescope explicit, and omitted the source proof. The source docstring and target expression are retained, including the level `1`, ordered parameters and implicit `{b n}` binders. Imports are narrowed to the three published dependencies, and unrelated declarations and unused namespace openings are omitted. No global instance is introduced.

The original copyright, author and Apache-2.0 header is retained. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. The statement alone proves no convergence, cohomology or reciprocity assertion.
