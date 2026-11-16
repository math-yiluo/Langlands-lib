# Low-degree Herbrand quotients of deep normal-basis unit subgroups

This is the exact proposition target that sufficiently deep chosen normal-basis principal-unit subgroups have subsingleton degree-zero and degree-minus-one Herbrand quotients. It quantifies over a Galois generator and every subgroup with the prescribed carrier, and uses the actual restricted Galois action. This file supplies the target for a separate proof task.

## Pinned source and name map

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisCohomology.lean`, M156.001. The source statement is lines 41–50 (docstring at 39–40), with section variables at lines 31–37 and the original proof at lines 51–111. File SHA-256: `74e06c12b2aec7982c7d82a47079fdca8ab4a51f856102abf57fedd3f3288d9b`.

The [readable pinned original](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisCohomology.lean>) is registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.exists_chosenNormalBasisPrincipalUnit_herbrand_subsingleton` | `Langlands.NYLL.LocalClassFieldTheory.exists_chosenNormalBasisPrincipalUnit_herbrand_subsingletonStatement` |

## Complete telescope and conclusion

The complete source section telescope is explicitly bound, retaining its single shared universe, order and binder kinds:

```lean
(K L : Type u)
[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L] [IsGalois K L]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
[ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
[IsNonarchimedeanLocalField L]
[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
[IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
```

The declaration then retains the explicit `(g : Gal(L/K))` and `(hgen : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)`. The latter generator assumption remains in the telescope even though it is not used to form the proposition's body.

The body is the original existential cutoff: there is `c : Nat` such that for every `n ≥ c`, every subgroup `V` of `𝒪[L]ˣ` whose carrier equals `chosenNormalBasisPrincipalUnitSet K L n` has subsingleton `HerbrandH0 (Gal(L / K)) V` and `HerbrandHMinusOne (Gal(L / K)) V g`. The source `letI` installs `chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV` before these two quotient types. The order of quantifiers, the explicit subgroup and carrier equality, the conjunction and the generator in degree minus one are unchanged.

These are the published concrete multiplicative quotient types: `HerbrandH0` is the fixed subgroup modulo the norm image restricted to it, and `HerbrandHMinusOne` is the norm kernel modulo the coboundary image restricted to it. They carry the actual Galois action restricted to `V`, using the published M145.005 stability proof through the published M145.006 construction.

## Published dependencies and modifications

The two imports are published `NormalBasisGaloisAction.PrincipalUnitSubgroupAction` and `HerbrandLowDegree.Basic.HerbrandQuotients.Definitions`. The original recursive-lifting import supplies proof dependencies; the target itself only needs these concrete action and quotient constructions. No recursive-lifting theorem is required to form the target, and no missing proof has been replaced by an assumption or another target.

Worker 197 prefixed the namespace with `Langlands.NYLL`, added the `Statement` suffix, changed the theorem into a `Prop`-valued `def`, explicitly bound the full source section telescope, narrowed the imports and omitted the original proof. The original docstring, complete target body and local-instance binding are retained; unrelated namespace openings are omitted. Explicit binding preserves the source theorem's assumptions, including its generator hypothesis, when elaborating a proposition definition. The local file option `linter.unusedVariables false` suppresses the warning for the intentionally retained `hgen`; it changes no declaration type or target body. No new instance is registered.

The original copyright, author and Apache-2.0 header is retained. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. The target is stated here; its proof, the recursive lifting theorems and any host class-formation or reciprocity consequences remain separate obligations.
