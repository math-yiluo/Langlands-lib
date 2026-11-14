# Normality of the extension subgroup of an embedded finite Galois extension

`Langlands.NYLL.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal`
proves exactly
`Langlands.NYLL.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normalStatement K L i`
for fields `K L : Type` (universe zero), an algebra `K → L`, `[IsGalois K L]`
and a `K`-algebra embedding `i : L →ₐ[K] SeparableClosure K`, with these
binders explicit and in the order of the target. Writing
`G₀ = closedFixingSubgroup K (SeparableClosure K) ⊥`, the statement says that the
fixing subgroup of the image `i(L)`, viewed as a subgroup of `G₀` through the
published `extensionSubgroup` (that is, `Subgroup.subgroupOf`), is a normal
subgroup of `G₀`.

## Instance registration

The source declaration is an `instance` of the Prop-valued class
`Subgroup.Normal`. It is ported as a `theorem` whose type is the published target
applied to its parameters, immediately followed by

```lean
attribute [instance] finiteGaloisExtensionSubgroupOfEmbedding_normal
```

so it is registered as a global instance under the source name. The target is a
reducible `abbrev`, so the instance is indexed by its unfolded
`Subgroup.Normal (extensionSubgroup …)` type. A private development check (not
part of this submission) confirmed that, with this module imported, instance
synthesis proves the source type
`(extensionSubgroup G₀ (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) …).Normal`
by this instance, and that the quotient group of `G₀` by this subgroup, which the
downstream M090.009 definition needs, is formed by instance search. Without the
registration, synthesis does not unfold the non-reducible
`finiteGaloisClosedFixingSubgroupOfEmbedding` and does not find the published
`closedFixingSubgroup_normal` instance.

## Implemented proof

The proof is the source script. `change` replaces
`finiteGaloisClosedFixingSubgroupOfEmbedding K L i` by its definition
`closedFixingSubgroup K (SeparableClosure K) (finiteGaloisFieldRangeOfEmbedding K L i)`
(a definitional unfolding; the target abbreviation unfolds as well). Then
`infer_instance` closes the goal. A development trace shows the instance chain:

1. Mathlib's `Subgroup.normal_subgroupOf` (`[H.Normal] → (H.subgroupOf K).Normal`),
   matched through the reducible `extensionSubgroup`;
2. the published instance
   `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_normal` (M089.004),
   which makes the fixing subgroup of a Galois intermediate field normal in
   `Gal(SeparableClosure K / K)`;
3. the published instance
   `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois`
   (M090.003), which makes `i(L)` Galois over `K` from `[IsGalois K L]`.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Dependencies

The module imports only the target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Normality.Statements`,
which supplies, directly or through its imports, `extensionSubgroup` (M004.002),
`closedFixingSubgroup` (M087.001), `fixingSubgroupLeBase` (M089.002),
`closedFixingSubgroup_normal` (M089.004) and the realization declarations
M090.001, M090.003 and M090.005. It does not use the source's
`extensionSubgroupBase_normal` (M089.005).

## Source and modifications

Adapted by Worker 447 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean`
(SHA-256 `c3681d1d4a2363fb2b1a28fb984b458e8051e97c30c3d4ec66bc43608b1f44b2`),
unit M090.006: docstring lines 71–72, instance lines 73–89. The source is readable
under `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`. Registered sources: `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Modification record:

- `noncomputable instance … : (extensionSubgroup …).Normal` is replaced by a
  `theorem` whose conclusion is the published target
  `finiteGaloisExtensionSubgroupOfEmbedding_normalStatement K L i`, followed by
  `attribute [instance]` registering it under the source name; `noncomputable`
  is dropped because a theorem carries no data.
- The source section variables (lines 32–33) are replaced by the explicit binders
  of the target; `[FiniteDimensional K L]` is not a binder because the source
  instance does not keep it.
- The namespace is prefixed with `Langlands.NYLL`; `open KummerTheory` and the
  `noncomputable section` are omitted; the source imports are replaced by the
  target module.
- The docstring and the `change`/`infer_instance` proof (lines 81–89) are kept
  verbatim.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice. The
original license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support proof does not discharge any host class-formation, cup, transfer,
Tate or reciprocity target.
