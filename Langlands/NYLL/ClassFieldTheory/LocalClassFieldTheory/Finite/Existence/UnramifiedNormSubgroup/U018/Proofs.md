# The unramified norm subgroup as a valuation kernel

The theorem
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom`
has exactly the published type
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHomStatement`.
It proves
`MonoidHom.ker (valuationModDegreeMulHom K n) = unramifiedNormSubgroup K n`
for arbitrary `K : Type u`, with
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
and every `n : Nat`. The equality retains the source orientation and includes
`n = 0`.

## Implemented proof

The proof introduces the closed target's parameters and uses subgroup
extensionality. For a field unit `x`, `MonoidHom.mem_ker` rewrites kernel
membership as `valuationModDegreeMulHom K n x = 1`. The `change` step unfolds
the published subgroup carrier and the multiplicative and additive reduced
valuation maps. It converts the goal definitionally to

```text
(valuationMap K (Additive.ofMul x) : ZMod n) = 0
  ↔ (n : Int) ∣ valuationMap K (Additive.ofMul x).
```

Mathlib's `ZMod.intCast_zmod_eq_zero_iff_dvd` proves this equivalence for every
natural modulus, including zero. No surjectivity result or positivity
hypothesis is needed.

The sole direct import is the published
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.SubgroupStatements`.
Its imports supply the unchanged subgroup, valuation maps and Mathlib criterion.
This proof establishes the kernel description of the already defined subgroup.
Identification with an actual extension norm subgroup is a separate result.

## Source correspondence and attribution

The original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`,
M266.018, theorem
`LocalClassFieldTheory.unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom`,
lines 186–191 (the task's cited range includes line 192).
The source is registered as `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The full source file has SHA-256
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`
and was read in full. No applicable project errata note was found.

The original proof uses subgroup extensionality and rewrites with the source
membership and multiplicative divisibility lemmas, M266.012 and M266.009.
The implemented proof retains extensionality, unfolds the definitions directly,
and applies the same Mathlib divisibility criterion used by the original
M266.004 beneath M266.009. It imports no unreviewed helper proofs.
Worker 209 added the `Langlands.NYLL` namespace prefix, the modification record,
the exact named proposition annotation, and this direct proof adaptation.
The original hypotheses, universe generality and equality are unchanged.

The original copyright and author header is retained. The Apache-2.0 license
and notices are published in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No other worker's unpublished draft was reused.
