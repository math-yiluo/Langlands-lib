# Actual integral-closure complete-DVF existence target

This module defines the single closed proposition
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.ExistsIntegralClosureStandardCompleteDVFStatement.{u,v,w}`.
It states NYLL source unit M245.017 without proving it. Its complete unapplied
Lean type is `Prop`; only the independent universe levels `u`, `v` and `w` are
declaration parameters.

All mathematical parameters occur inside the proposition, in this order:

1. A field carrier `K : Type u` and extension carrier `L : Type w`.
2. Instances `[Field K]`, `[Field L]`, the supplied `[Algebra K L]`, and
   `[FiniteDimensional K L]`.
3. A chosen bundle
   `base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K`.
4. The separability instance `[Algebra.IsSeparable K L]` for that same algebra.

The conclusion is exactly

```lean
∃ target : CompleteDVF.{w, 0} L,
  (∀ z : L,
    z ∈ target.valuation.valuationSubring ↔
      z ∈ (integralClosure base.valuation.valuationSubring L).toSubring) ∧
  ∃ _ : (integralClosure base.valuation.valuationSubring L) ≃+*
    target.valuation.valuationSubring, True
```

Here `CompleteDVF` is the published bundle in
`Langlands.NYLL.ValuationTheory.DiscreteValuationField`. Its field carrier is
`L : Type w`, while its chosen value-group carrier is in `Type 0`. The supplied
base value group remains in the independent universe `v`. The target stores
rank-one discreteness and completeness of its actual valuation subring for
its canonical maximal-ideal adic topology.

Write `A = base.valuation.valuationSubring`. This is the actual valuation
subring of `K`, with its inclusion in `K`. Mathlib's induced `A`-algebra
structure on `L` uses that inclusion followed by the supplied `algebraMap K L`.
The expression `integralClosure A L` is Mathlib's subalgebra of elements of
this same `L` integral over `A`; `.toSubring` retains exactly its carrier.
The first conjunct compares membership for every element of `L`. Both
conjuncts use the same existential `target`. The second conjunct asserts the
existence of a Mathlib `RingEquiv` from the actual integral closure to that
target's valuation subring. Its final `True` preserves the source formulation
of existence of this data inside `Prop`.

The supplied algebra structure is arbitrary; no proper-extension condition
excludes `L = K`. The target assumes no chosen extension valuation, valuation
extension, localness or DVR structure on the integral closure, maximal-ideal
completeness of that closure, or conclusion certificate. This statement unit
introduces no data construction, global instance or theorem proof. Valuation
extension, fundamental identities, uniqueness and local reciprocity are
separate obligations.

## Source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/FiniteIntegralClosure.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709` in
`n-yamaguchi-0729/ClassFieldTheory`. Its SHA-256 is
`43c21425b2c39e7e6e5d2bca1f2b615c5c29e9d91e69d32d079e593df3170094`.
The complete assertion and proof at lines 513-629 were read, together with
lines 1-64, including the independent universe declaration at line 23 and
ambient field/algebra/finite-dimensional variables at lines 30-31.

| Original declaration | Adapted declaration |
| --- | --- |
| `ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_completeDVF`, M245.017, line 513 | `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.ExistsIntegralClosureStandardCompleteDVFStatement.{u,v,w}` |

The source's implicit ambient `K`, `L` and instances become internal universal
binders. The source's explicit `base` and subsequent separability instance
keep their relative order. Its abbreviations `base.valuationSubring` and
`target.valuationSubring` are expanded to `base.valuation.valuationSubring`
and `target.valuation.valuationSubring`. The existential target universe,
pointwise membership iff, ring equivalence and final `True` are unchanged.
The original proof constructs the discrete valuation from the actual integral
closure and transports its maximal-ideal completeness to the valuation
subring. That proof is not included in this statement module.

The source is retained in registered snapshot
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The registered attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable source erratum was found in the checked project and Library
notes on 31 October 2026. M245 has no compatibility edit in the recorded
patch10; none of that patch's implementations is reused here.

The imports reuse the published `CompleteDVF` from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`
and Mathlib's `FieldTheory.Separable`, `LinearAlgebra.FiniteDimensional.Defs`
and `RingTheory.IntegralClosure.Algebra.Basic`. The latter supplies the actual
`integralClosure`; existing Mathlib imports supply `RingEquiv` and the
valuation-subring algebra structures. No source theorem import is required
to express this proposition.

## Attribution and modifications

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The source is
Apache-2.0. Unmodified copies of its
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained in
`licenses/NYLL/`. The selected source has no source-specific entry in that
NOTICE; the applicable retained credits remain unchanged.

Worker 384 extracted and renamed this single theorem statement as a closed
Prop definition, added the `Langlands.NYLL` namespace prefix, made the
independent universe parameters explicit, internalized all mathematical
binders, expanded the two valuation-subring abbreviations, replaced the
source imports by the focused public and Mathlib imports above, and wrote
this Markdown on 31 October 2026. All other source declarations and the
selected theorem's proof are omitted. No implementation draft was supplied
by another project worker.

The source uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. This adaptation uses approved
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
