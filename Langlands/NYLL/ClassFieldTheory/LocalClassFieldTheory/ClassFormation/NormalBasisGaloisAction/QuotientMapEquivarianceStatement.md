# Galois equivariance of the integer-unit quotient map

Worker 197 adapts source unit M145.016 for Task 5874 revision 3.

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`.
The statement is at lines 256–263, its docstring at line 255 and its proof at line 264.
The original file has SHA-256
`5d4eeb8f1dc2a8efeef90ee3c9d89bb43c048d5057e49f32701cefc8768a05c6`.
The [readable pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean>)
is registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap_equivariant` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap_equivariantStatement` |

The proposition says that projecting the Galois translate of an integer unit
equals translating its class in the quotient by the supplied subgroup `V`.
The equality of the carrier of `V` with the chosen normal-basis principal-unit
set at level `n` is retained.

The complete effective source section telescope is made explicit, in its
original order and with its original binder kinds:

```lean
(K L : Type u)
[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
(n : Nat) (V : Subgroup 𝒪[L]ˣ)
(hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
(sigma : Gal(L/K)) (a : 𝒪[L]ˣ)
```

The two `letI` expressions install the actual published integer-unit Galois
action and the published M145.010 quotient action. The latter retains the
published stability proof M145.005 in its construction. The quotient map
is the published `QuotientGroup.mk' V` construction from `IntegerUnitMaps`;
no action or projection is supplied as an extra parameter.

Modifications: prefix the namespace with `Langlands.NYLL`, extract this focused
pair, replace the theorem by a `Prop`-valued definition with a `Statement` suffix,
make the complete effective telescope explicit and narrow the imports to the
published constructions. Preserve the source statement, local-instance order,
docstring and attribution. Omit the theorem proof and unrelated commands.
No global instance is introduced. The Apache-2.0 header and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

This contribution states equivariance; its proof is a separate task. It does
not complete the larger statement-layer task or prove a class-formation or
reciprocity theorem. Development checks use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.
