# Complete-DVF extension with its actual integral closure

This module defines exactly one closed proposition,
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u,v,w}`.
Its full unapplied Lean type is `Prop`; its only declaration parameters are
the independent universe levels `u`, `v` and `w`. It states the existence
consequence of source unit M245.018 and supplies no theorem proof.

Every mathematical parameter is universally quantified inside the body,
in this order:

1. The carriers `K : Type u` and `L : Type w`.
2. Instances `[Field K]`, `[Field L]`, the arbitrary supplied
   `[Algebra K L]`, and `[FiniteDimensional K L]`.
3. The supplied
   `base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K`.
4. `[Algebra.IsSeparable K L]` for that same algebra.

The conclusion is exactly

```lean
∃ target : CompleteDVF.{w, 0} L,
  ∃ hExt : _root_.Valuation.HasExtension base.valuation target.valuation,
    letI : _root_.Valuation.HasExtension base.valuation target.valuation := hExt
    IsIntegralClosure target.valuation.valuationSubring
      base.valuation.valuationSubring L
```

The published `CompleteDVF` bundle stores a chosen valuation, its rank-one
discreteness and the maximal-ideal adic completeness of its actual valuation
subring. The base field, base value group and extension field retain the
independent universes `u`, `v` and `w`. The existential target's field carrier
is this same `L`, and its value-group carrier lies in `Type 0`. Both conclusions
refer to that one target.

Write `A = base.valuation.valuationSubring` and
`B = target.valuation.valuationSubring`. Mathlib's actual
`Valuation.HasExtension` says that `base.valuation` is equivalent to the
comap of `target.valuation` along the supplied `algebraMap K L`.
It permits different value groups and valuation normalizations. The witness
`hExt` is a conclusion. The following `letI` installs precisely that witness
as a local instance.

The algebra `A → L` is the inclusion `A → K` followed by the supplied
`algebraMap K L`; the algebra `B → L` is the actual inclusion of the valuation
subring. Mathlib's instances
`Valuation.HasExtension.instAlgebra_valuationSubring`,
`instIsScalarTower_valuationSubring` and
`instIsScalarTower_valuationSubring'` provide the compatible algebra
`A → B` and towers `A → K → L` and `A → B → L` under this `hExt`.
In particular, the image in `L` of `algebraMap A B a` is
`algebraMap K L (a : K)`.

Mathlib's `IsIntegralClosure B A L` uses the two actual algebra maps into
`L`. It asserts injectivity of `algebraMap B L` and, for every `z : L`,
that `IsIntegral A z` holds if and only if
`∃ b : B, algebraMap B L b = z`. Thus the conclusion identifies the actual
integral elements inside the supplied `L`, with the compatible induced
scalar structures above. It is not an assertion about an unrelated ring
isomorphic to an integral closure.

The arbitrary supplied finite-dimensional separable algebra includes the
identity-extension case `L = K` with its identity algebra structure.
There is no proper-extension condition. There is no supplied upstairs
valuation, extension witness, closure comparison, localness or completeness
premise beyond `base : CompleteDVF`. The target and extension witness are
existential conclusions, as is the integral-closure property.

## Derived source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` in
`n-yamaguchi-0729/ClassFieldTheory`. Its full-file SHA-256 is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.
The source header, universe declaration at line 23, ambient
field/algebra/finite-dimensional variables at lines 30-31, and complete
M245.018 assertion and proof at lines 631-685 were read.

| Original declaration | Adapted declaration |
| --- | --- |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity`, M245.018, line 634 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u,v,w}` |

This is a deliberately derived, smaller consequence. The source signature
at lines 634-644 asserts the target, its `hExt`, and the conjunction of
`IsIntegralClosure` with the fundamental ramification identity
`degree = ramificationIndex * residueDegree`. This module retains the
existential witnesses and the first conjunct and omits the identity.
It therefore does not state the full source theorem.

The first part of the original proof obtains the target and its pointwise
integral-closure comparison from M245.017 at lines 645-647. It constructs
`hExt` at lines 648-656 by contraction of the integral closure, then
`hIntegralClosure` at lines 659-674 using the actual inclusion in `L`.
Only the later part at lines 675-685 invokes the fundamental identity.
These passages explain the provenance of the selected consequence; their
proof is not included here.

The original consumer M248.005,
`LocalFieldTheory.chosenLocalExtensionCompleteDVF_exists`, at lines 114-128
of
[`FiniteExtensionCompleteDVF.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionCompleteDVF.lean),
uses this existence consequence and explicitly discards the fundamental
identity at lines 125-128. That consumer has `K L : Type`; this target
retains the independent universes already present in M245.018.
The consumer's full-file SHA-256 is
`f9f4741aa6a1584e125f571e6095b641f13f0983ccbda6225d9324b9fdc1f27c`.

The source's ambient parameters become internal universal binders, keeping
the relative order of `base` and separability. The namespace receives the
`Langlands.NYLL` prefix. The source abbreviations `base.valuationSubring`
and `target.valuationSubring` expand to their
`valuation.valuationSubring` projections, and `_root_.Valuation.HasExtension`
explicitly names Mathlib's predicate. The target's universe, supplied
algebra, dependent `hExt`/`letI` structure and actual `IsIntegralClosure`
conclusion are retained.

The prerequisite M245.017 theorem is already published as
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF.{u,v,w}`
in
[StandardCompleteDVFProof.lean](StandardCompleteDVFProof.lean).
It gives a common complete-DVF target and the actual pointwise comparison
in `L`. Proving the present target still requires constructing its
`HasExtension` and `IsIntegralClosure` conclusions. Those are not supplied
as hypotheses or discharged by this statement definition.

The statement imports the published
`Complete.Definitions` module and Mathlib's `FieldTheory.Separable`,
`LinearAlgebra.FiniteDimensional.Defs`,
`RingTheory.IntegralClosure.IsIntegralClosure.Defs` and
`RingTheory.Valuation.Extension`. No source theorem or new global instance
is required to express it. A later exact-target proof, chosen extension
data, uniqueness, the fundamental identity, finite-module comparisons,
inertia and host reciprocity remain separate units.

## Attribution and modifications

The source is retained in registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with registered attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source erratum was found in the checked project and Library
notes on 31 October 2026.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The source is Apache-2.0. Unmodified copies of its
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in `licenses/NYLL/`.
The selected source and consumer have no source-specific entry in that
NOTICE; the applicable retained credits remain unchanged.

Worker 384 selected and renamed the existence consequence, removed the
fundamental-identity conjunct and all proofs, converted the selected
statement to a closed Prop definition, internalized all mathematical
parameters, retained the three independent universes, prefixed the
namespace, expanded the valuation-subring abbreviations, qualified
`HasExtension`, replaced the source imports as listed above, and wrote
this Markdown on 31 October 2026. M245 and M248 have no compatibility edit
in the recorded feasibility patch10. No implementation draft or patch
from another worker is reused here.

The source uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. This adaptation uses approved
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
