# Normal-basis subgroup norm, coboundary and inclusion targets

These three propositions state compatibility of the actual restricted Galois action on a normal-basis principal-unit subgroup with its inclusion into the integer units. They are statement targets; no proof of any of these propositions is supplied here.

## Pinned source and correspondence

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean` (file SHA-256 `5d4eeb8f1dc2a8efeef90ee3c9d89bb43c048d5057e49f32701cefc8768a05c6`).

The [readable pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean>) is registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Source unit and declaration | Source statement lines | Adapted declaration |
| --- | --- | --- |
| M145.008 `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe` | 169–176 (proof through 185) | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coeStatement` |
| M145.009 `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe` | 189–196 (proof through 199) | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coeStatement` |
| M145.015 `LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariant` | 245–252 (proof at 253) | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariantStatement` |

## Objects and complete source telescopes

All three definitions retain the same ordered section telescope from source lines 92–94 and 120–122:

```lean
(K L : Type u)
[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L]
```

The two fields share the single universe `u`. The unused generic-action universes `uG` and `uA` in the original file supply no parameters to these declarations. `K` and `L` are explicit, and all the displayed instances retain their source order. Writing this telescope explicitly preserves hypotheses that a statement-only `def` could otherwise omit.

For M145.008 the remaining explicit parameters, in order, are:

```lean
(n : Nat) (V : Subgroup 𝒪[L]ˣ)
(hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
(a : V)
```

For M145.009 and M145.015, `(sigma : Gal(L/K))` occurs immediately before `(a : V)` in that list. There is no positivity assumption on `n`, topology on `L`, or additional group-action parameter.

The equality `hV` identifies the subgroup carrier with the chosen normal-basis principal-unit set at level `n`. Every target first installs `chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV` on `V`, then `galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L` on `𝒪[L]ˣ`, exactly as in the source statement.

M145.008 says that taking the Tate norm in `V` and then coercing to `𝒪[L]ˣ` gives the ambient Tate norm. The published `tateNorm` is the finite product over `Gal(L / K)` of the Galois translates. M145.009 says the same for `sigmaMinusOne`, the multiplicative expression `sigma • a * a⁻¹`. M145.015 says that the published subgroup inclusion commutes with each Galois element. All three are equalities of actual integer units.

## Published dependencies and modifications

The subgroup action is imported from `NormalBasisGaloisAction.PrincipalUnitSubgroupAction`. It retains the actual stability proof from `NormalBasisGaloisAction.U005.Proofs` through its imports. The subgroup inclusion is reused from `NormalBasisGaloisAction.IntegerUnitMaps`; the low-degree operations are reused from `HerbrandLowDegree.Basic.Definitions` in `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand`. Thus the action and maps are the published data constructions, and their prerequisite proofs are not replaced by assumptions or statement targets.

Worker 197 extracted these three related statements into one focused file, prefixed the namespace with `Langlands.NYLL`, appended `Statement` to the theorem names, changed `theorem` to `def ... : Prop :=`, and omitted the theorem proofs and the first two source `@[simp]` attributes. The original docstrings and target expressions, including both ordered `letI` bindings, coercions and binder kinds, are retained. Imports are narrowed to the three published modules above; unrelated source declarations and unused `open` commands are omitted. No global instance is added.

The original copyright, author and Apache-2.0 header is retained. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. These statement targets alone establish no class-formation or reciprocity theorem.
