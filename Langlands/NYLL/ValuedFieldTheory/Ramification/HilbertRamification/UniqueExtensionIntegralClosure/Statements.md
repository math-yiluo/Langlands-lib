# Unique-extension valuation-ring endpoints: proposition targets

This module defines four closed propositions in
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher`.
They state the endpoint conclusions of NYLL M308.005–.008 for the actual chosen
discrete valuation fields. This unit supplies statements only; it supplies no
proof of these propositions and installs no conclusion as a typeclass instance.

## Source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/UniqueExtensionIntegralClosure.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/UniqueExtensionIntegralClosure.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, with SHA-256
`d87856edbb266e6f2c5e924d6657cd48093dd8fb700d33664ec87566832d3efd`.
The shared source context is at lines 27–40. Each original name in the table
belongs to `RamificationTheory.HilbertRamification.Higher`; each target belongs
to that namespace prefixed by `Langlands.NYLL`.

| Unit | Original name | Signature lines | Full theorem lines | Target name |
| --- | --- | --- | --- | --- |
| M308.005 | `target_valuationSubring_element_isIntegral_of_uniqueExtension` | 149–153 | 149–181 | `target_valuationSubring_element_isIntegral_of_uniqueExtensionStatement` |
| M308.006 | `target_valuationSubring_isIntegral_of_uniqueExtension` | 185–188 | 185–191 | `target_valuationSubring_isIntegral_of_uniqueExtensionStatement` |
| M308.007 | `target_valuationSubring_isIntegralClosure_of_uniqueExtension` | 195–198 | 195–203 | `target_valuationSubring_isIntegralClosure_of_uniqueExtensionStatement` |
| M308.008 | `target_valuationSubring_moduleFinite_of_uniqueExtension` | 208–211 | 208–218 | `target_valuationSubring_moduleFinite_of_uniqueExtensionStatement` |

These are the actual command boundaries in the pinned file; the task's broader
line ranges for the last three endpoints overlap neighboring text.
The snapshot is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The existing attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No source-specific NYLL erratum was found in the project errata lookup.

## Full hypotheses and universes

Every definition has type `Prop` and universally quantifies the following
context inside its body, in source order:

```lean
∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
  {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
  [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
  [IsGalois K L]
  (huniq :
    Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
      base target),
  ...
```

The first definition additionally quantifies `(a : target.valuationSubring)`
after `huniq`. There is no element parameter in the other three definitions.
The carrier types and valuation bundles are implicit binders; field structures,
the field algebra, finite dimensionality, extension compatibility and the Galois
condition are instance binders; `huniq` and the first target's `a` are explicit.
All four universe levels are independent: `u` for `K`, `v` for the base value
group, `w` for `L`, and `x` for the target value group. The uniqueness predicate's
fifth universe is explicitly `x`, exactly as in each source endpoint.

The published `DVF` stores its valuation and rank-one discreteness. The published
`HasUniqueValuationExtension` says that every valuation on `L` with comparison
value group in `Type x` extending the base valuation is equivalent to the chosen
target valuation. The separate `HasExtension` hypothesis says that the chosen
target itself extends the base along the supplied `algebraMap K L`, up to
valuation equivalence. Finite dimensionality and `IsGalois K L` are retained
even where the conclusion alone does not mention them. There is no completeness,
Henselian, local-field or residue-separability premise, and no premise assuming
any of the four conclusions.

## Conclusions and actual scalar structures

| Target | Body after the shared hypotheses (and `a` for the first) | Meaning |
| --- | --- | --- |
| Element integrality | `IsIntegral base.valuationSubring a` | The element `a` in the target valuation ring satisfies a monic polynomial over the base valuation ring, evaluated in the target valuation ring. |
| Algebra integrality | `Algebra.IsIntegral base.valuationSubring target.valuationSubring` | Every element of the target valuation ring is integral over the base valuation ring. |
| Integral closure | `IsIntegralClosure target.valuationSubring base.valuationSubring L` | The target valuation ring embeds in `L`, and its image is exactly the set of elements of `L` integral over the base valuation ring. |
| Module finiteness | `Module.Finite base.valuationSubring target.valuationSubring` | The target valuation ring has a finite set of generators as a module over the base valuation ring. |

Here `base.valuationSubring` and `target.valuationSubring` are the published
`DVF.valuationSubring` abbreviations for the chosen valuations' actual
valuation subrings. They are not abstract replacement rings.
Mathlib's `Valuation.HasExtension.instAlgebra_valuationSubring` supplies the
algebra between them. Its algebra map is the restriction of the supplied field
algebra map: `Valuation.HasExtension.coe_algebraMap_valuationSubring_eq` states
that for `r : base.valuationSubring`, its image in `L` equals
`algebraMap K L (r : K)`. The canonical subring embeddings supply the ambient
algebras in the integral-closure predicate. Its argument order is target ring,
base ring, then ambient field `L`. No custom algebra or module structure is
introduced.

## Extraction and modifications

Worker 545 made this focused extraction on 14 November 2026:

- Prefix the source namespaces with `Langlands.NYLL` and append `Statement` to
  each endpoint name.
- Replace each source theorem and its proof with a closed Prop-valued `def`.
  Move its full source context, including proof-only hypotheses and explicit
  `huniq`, into universal quantifiers inside the proposition. Preserve the
  conclusions, binder order, implicit and instance binder kinds, and universes.
- Replace the broad NYLL imports and `Mathlib.Algebra.Polynomial.Lifts` with
  the published `RealLowerGroups.UniqueExtension`,
  `Mathlib.FieldTheory.Galois.Basic`, and
  `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs`.
  The first import already exposes the published DVF data and Mathlib valuation
  extension algebra. The other two supply the endpoint predicates and field
  hypotheses.
- Omit the unused source namespace opens, polynomial scope, and
  `noncomputable section`; fully qualify the reused NYLL objects. Rewrite
  documentation for the statement-only boundary and omit all source proof code.
  No orbit-polynomial construction or auxiliary theorem is copied.

The original proof route uses M308.001–.004 for orbit-polynomial construction,
monicity, invariance and coefficient descent. The integral-closure proof then
calls M110.036, `valuationSubring_isIntegralClosure_of_isIntegral`, and the
finiteness proof calls `moduleFinite_valuationSubring_of_isIntegralClosure`.
Those are future proof dependencies, not hypotheses of these targets.
Earlier-unit work remains with Task 5264; this unit adds no earlier-unit
duplicate. The M316 fixed-field valuation-ring construction and the later
Herbrand quotient chain can use proofs of these targets once independently
published.

## Attribution

The Lean header retains the original notice verbatim: copyright (c) 2026
Naganori Yamaguchi, all rights reserved; released under Apache 2.0; authors
Naganori Yamaguchi (assisted by OpenAI Codex). The adaptation adds its own
modification notice. The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) remain the applicable NYLL
attribution files. The original NOTICE has no entry specific to
`UniqueExtensionIntegralClosure.lean`.
