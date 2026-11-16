# Galois action on a normal-basis principal-unit graded quotient

This definition constructs the actual multiplicative distributive action of `Gal(L / K)` on `Vn / Vsucc`, represented as the normal-basis principal-unit successive quotient. The action descends the published restricted action on `Vn`, using the published proof of stability at level `n+1`.

## Pinned source and name map

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGradedLifting.lean`, M154.002, lines 75–99 (attribute at 74, docstring at 72–73). The file SHA-256 is `c86a5154f1ba4d19d41079de279f16163f4c8044143370a3177033440af445ae`.

The [readable pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGradedLifting.lean>) is registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction` |

This is same-module dependency closure for the required M154.003 and M154.004 targets. It remains action data, including its proof terms.

## Complete telescope

The source section variables at lines 30–35 are retained in their original order:

```lean
(K L : Type u)
[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

The types share universe `u`; the types are explicit and the hypotheses are instance binders. The declaration then has:

```lean
(n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
(hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
(hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
  chosenNormalBasisPrincipalUnitSet K L (n + 1))
```

Thus `Vn` and `Vsucc` stay implicit, while the level, subgroup inclusion and two carrier equalities stay explicit. There is no positivity premise on `n` and no topology on `L`. The return type is `MulDistribMulAction (Gal(L / K)) (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)`.

## Retained construction and published prerequisites

The body first installs `galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L`, followed by `chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n Vn hVn`. The target quotient is definitionally `Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV`. The published generic constructor `quotientMulDistribMulActionOfSubgroupStable` descends the action to this quotient.

Its stability certificate is the source proof term, unchanged. It uses `mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff` to express membership in the successor subgroup, changes the restricted action to the ambient integer-unit action, rewrites with `hVsucc`, and applies `galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet` at level `n+1`. Consequently the action sends a representative's class to the class of its actual Galois translate.

All these prerequisites are imported by their published Lean names:

- `NormalBasisGaloisAction.PrincipalUnitSubgroupAction` supplies the actual subgroup action and imports the actual M145.005 stability proof from `.U005.Proofs`.
- `NormalBasisGaloisAction.QuotientDistribAction.Definitions` supplies the existing generic quotient construction, including its original proof fields.
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U109.U109.Proofs` supplies the actual membership equivalence and imports the successive subgroup, quotient and quotient-map data.

No missing proof is replaced by a hypothesis or a statement target.

## Modifications and attribution

Worker 197 extracted this definition, prefixed the namespace with `Langlands.NYLL`, and narrowed the imports to the three published prerequisites above. The effective section telescope, declaration binders, return type, body, local instance order, embedded proof and `@[implicit_reducible]` attribute are retained. The original docstring is retained; unrelated declarations and unused namespace openings are omitted. The definition is not registered as a global instance.

The original copyright, author and Apache-2.0 header is retained. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. This action construction alone establishes no graded equivariance, cohomological lifting or reciprocity theorem.
