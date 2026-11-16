# Surjectivity of multiplication into a successive ideal quotient (M133.030)

`Langlands.NYLL.LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_surjective`
proves the exact published proposition
`Langlands.NYLL.LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_surjectiveStatement K ϖ hϖ n`.
The theorem retains arbitrary `K : Type u`, `[Field K]`, `[ValuativeRel K]`,
`[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, an arbitrary
`ϖ : 𝒪[K]`, its proof `hϖ : Irreducible ϖ`, and every `n : Nat`, including zero.
It states surjectivity of the actual linear map
`r ↦ [r * ϖ ^ n]` into `MaximalIdealPowSuccQuot K n`.

After exposing surjectivity with `change`, the proof applies the published
`MaximalIdealPowSuccQuot.inductionOn` to a quotient class. Its motive asks for
a coefficient whose image is that class, so it suffices to construct the
coefficient for an element `a` of the ideal `𝓂[K] ^ n`.
The published M133.021 theorem
`maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible` rewrites the
membership proof `a.2` into membership in `Ideal.span {ϖ ^ n}`.
A `show` exposes that theorem's named Prop target as the equality needed by
`simpa`. Mathlib's `Ideal.mem_span_singleton` then supplies `r` and an
equation `hr : (a : 𝒪[K]) = ϖ ^ n * r`.

The proof chooses that `r` and exposes the quotient projections with `change`.
It proves equality of their ideal-valued representatives using `ext` and
`simp [maximalIdealPowMulUniformizerPowMap, hr, mul_comm]`, and rewrites with
that equality. This is the original representative proof, and it uses no
kernel assertion or chosen-uniformizer restriction.

The only direct imports are the published target/construction module
`IdealQuotients.UniformizerPowMap.Definitions` and the two proof modules
`PrincipalUnitQuotients.U062.Proofs` and `IdealQuotients.U021.Proofs`,
all under
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField`.
No private helper or additional premise is introduced.

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
`LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap_surjective`,
M133.030, lines 464–485 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source file SHA-256 is
`8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
It is readable below
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Worker 642 extracted the proof on 16 November 2026, added the
`Langlands.NYLL` namespace prefix, replaced whole-source imports with the
published modules above, wrote the theorem type as the exact named Prop target,
and added the initial `change` and the `show` in the ideal-power rewrite.
The remaining source proof is preserved.
No published statement or imported file is modified.
The original copyright, Apache-2.0 license and author header are retained
verbatim in the Lean file. The original `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This proof establishes the specified local-field support proposition.
