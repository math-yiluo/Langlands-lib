# Comparison of chosen and supplied local valuations: proof

This module proves the exact published closed proposition
`Langlands.NYLL.LocalFieldTheory.ChosenLocalExtensionSuppliedComparisonStatement`.
Its sole theorem is
`Langlands.NYLL.LocalFieldTheory.chosenLocalExtension_suppliedComparison`,
in entry module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenSuppliedComparisonProof`.
The complete unapplied theorem type is:

```lean
theorem chosenLocalExtension_suppliedComparison :
    ChosenLocalExtensionSuppliedComparisonStatement
```

There are no free mathematical arguments or universe parameters. The
[published statement pair](ChosenSuppliedComparisonStatement.md) and its
imported definitions are preserved.

## Target and conventions

The target internally quantifies over `K L : Type`, their supplied `Field`
structures, `Algebra K L`, `FiniteDimensional K L` and
`Algebra.IsSeparable K L`. Both fields have their own supplied `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` structures. Its final
premise is the raw
`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
along the supplied `algebraMap K L`.

The conclusion is the conjunction of
`(chosenLocalExtensionCompleteDVF K L).valuation.IsEquiv
  (localCompleteDVF L).valuation`
and equality of their actual `ValuationSubring L` objects. `IsEquiv` asserts
equivalence of the inequalities on every pair of elements of `L`, with the
chosen valuation first. It allows distinct value groups and normalizations.
The equality identifies the subrings inside the same `L`, whose elements have
valuation at most one. The canonical projection on the right is
definitionally the valuation of the supplied upstairs valuative relation.
The identity extension is included.

## Implemented proof

The proof introduces `K`, `L` and all twelve instance binders of the target,
including the independently supplied upstairs structures and raw extension
premise. It then installs one local instance:

```lean
let : Valuation.HasExtension (localCompleteDVF K).valuation
    (localCompleteDVF L).valuation :=
  localCompleteDVFValuation_hasExtension K L
```

The imported [canonical extension proof](ExtensionProof.md) gives this
instance from the supplied raw premise. Both extension relations use the
same supplied algebra map; `HasExtension` means that the base valuation is
equivalent to the upstairs valuation pulled back along that map.

Next, the imported [chosen uniqueness theorem](ChosenUniquenessProof.md)
is applied to `K`, `L` and exactly `(localCompleteDVF L).valuation`.
Its comparison value group is the stored value group of that canonical
package, in universe zero. The local instance just constructed meets its
compatibility premise. The result `hEquiv` is exactly the first conjunct,
with the named chosen valuation as its first argument.

Finally, Mathlib's `Valuation.isEquiv_iff_valuationSubring`
(`Mathlib/RingTheory/Valuation/ValuationSubring.lean:450–457` at the approved
pin) converts `hEquiv` to equality of those two actual subrings. Pairing
`hEquiv` with this equality proves the target. This final step needs no
identification of the value groups.

Only the local compatibility instance is installed. The theorem retains the
supplied upstairs structures throughout. The finite separable hypotheses
enter through the named chosen construction and its published uniqueness
theorem. The proof imports the target, canonical extension proof and chosen
uniqueness proof by Lean module name and introduces no helper declarations.

## Development check

The exact unapplied theorem compiles in the approved environment with zero
errors and warnings. Inspection reports no universe parameters and only
`propext`, `Classical.choice` and `Quot.sound`. Independent exact-target
validation, semantic review and publication are separate from this development
check.

## Derived provenance and attribution

This combined comparison is derived from the published adaptations of Naganori
Yamaguchi's NYLL results; it is not a literal upstream declaration. The original
source is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Worker 1199 read the
complete 206-line file and verified SHA256
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.

| Original unit | Role in this derived proof |
| --- | --- |
| M248.001, lines 34–55, `localCompleteDVF` | Packages each supplied local-field valuation. |
| M248.002, lines 58–74, `localCompleteDVFValuation_hasExtension` | Its published adaptation transfers the raw compatibility premise. |
| M248.006, lines 130–138, `chosenLocalExtensionCompleteDVF` | The published named chosen valuation is preserved. |
| M248.011, lines 194–204, `chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension` | Its published closed uniqueness adaptation supplies the chosen-first equivalence. |

The original M248.011 invokes a generic uniqueness theorem. The published
adaptation used here proves its local specialization directly by
integral-closure containment and dimension-one overring rigidity, as explained
in its own paired Markdown. This module composes those accepted results with
the Mathlib subring criterion; it copies no upstream tactic proof.

The registered sources are `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable errata file was found in the workspace, project notes or
current Library.

The original copyright and author header is retained verbatim. The inherited
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged. Worker 785
authored the published canonical and chosen adaptations and canonical extension
proof; Worker 1199 authored the published chosen uniqueness proof. These
published results are imported, with their existing attribution preserved.
Worker 106 supplied the target formulation, routing and suggested composition
route, without a proof draft, and is credited for that composition guidance.
Worker 1199 implemented this proof and wrote this explanation on 1 November
2026. Both workers are listed as contributors to this unit. No unpublished
draft was reused.

The approved environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; upstream used Lean 4.35.0-rc2
and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The result concerns the exact Type 0 comparison target. Host inertia, finite
reciprocity, arbitrary-universe field transport, cohomological agreement and
Weil-system results remain separate.
