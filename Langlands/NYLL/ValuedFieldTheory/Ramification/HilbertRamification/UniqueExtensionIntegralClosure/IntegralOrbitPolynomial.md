# The full integral-orbit polynomial

Worker 556, 14 November 2026.

This module defines
`Langlands.NYLL.RamificationTheory.HilbertRamification.Higher.integralOrbitPolynomial`
in
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.UniqueExtensionIntegralClosure.IntegralOrbitPolynomial`.
It extracts the data definition M308.001 from Naganori Yamaguchi's NYLL
`UniqueExtensionIntegralClosure.lean`, lines 44–52, at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.

## Polynomial and coefficient ring

For `a : target.valuationSubring`, the definition is exactly

```lean
∏ σ : Gal(L/K),
  (Polynomial.X - Polynomial.C
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a))
```

Its coefficient ring is the actual chosen `target.valuationSubring`, the
subring of `L` consisting of `z` with `target.valuation z ≤ 1`.
`Polynomial.X` and each `Polynomial.C` in the product belong to
`Polynomial target.valuationSubring`. The published
`valuationSubringAutOfUniqueExtension` is a ring automorphism of this very
subring; its value on `a` has underlying field element `σ (a : L)`.
Its membership proof uses uniqueness of valuation extension.

`Gal(L/K)` is Mathlib notation for all `K`-algebra automorphisms `L ≃ₐ[K] L`.
The finite product has one factor for every such automorphism. Repeated
images of `a` remain repeated factors: this construction does not take the
set of distinct conjugates or select coset representatives.

## Complete parameter scope

The four universe levels `u v w x` are independent. With
`Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF` opened, the
complete parameter context is:

```lean
{K : Type u} {L : Type w}
[Field K] [Field L] [Algebra K L]
{base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
{target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
[FiniteDimensional K L]
[base.valuation.HasExtension target.valuation]
(huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
(a : target.valuationSubring) :
  Polynomial target.valuationSubring
```

Here `u` and `w` are the field carrier universes, and `v` and `x` are the
value-group universes of the chosen base and target DVFs. The uniqueness
predicate is specialized at exactly `u, v, w, x, x`: it quantifies over
competing valuations of `L` with value group in `Type x`. These competitors
need not be discrete. It says each competitor extending the base is
equivalent to the chosen target valuation. The separate extension instance
asserts compatibility of the chosen target with the supplied `Algebra K L`,
using its actual `algebraMap K L`.

Finite dimensionality supplies finiteness of the algebra automorphism
group. The `classical` command is inside the definition, where the finite
enumeration for the product is selected. The definition is marked
`noncomputable`; this module introduces no global or scoped instance and
requires no external `Fintype` parameter.

The surrounding original source section declares `[IsGalois K L]`, but
this variable is unused in the definition and Lean omits it from the
declaration. The extracted context has precisely the actual dependencies
above. There is no completeness or Henselian hypothesis.

The entry module compiled without warnings in the approved environment.
A private development check also assigned the entire unapplied constant
`@integralOrbitPolynomial.{u,v,w,x}` to the displayed telescope and compiled
successfully, confirming its parameter order without supplying any arguments.

## Source correspondence and modifications

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/UniqueExtensionIntegralClosure.lean`, lines 44–52](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/UniqueExtensionIntegralClosure.lean#L44-L52).
The full source file has SHA-256
`d87856edbb266e6f2c5e924d6657cd48093dd8fb700d33664ec87566832d3efd`;
its complete contents were read for this extraction.
The public partition records no patch10 modification for M308.

| Original source | Adaptation |
| --- | --- |
| `RamificationTheory.HilbertRamification.Higher.integralOrbitPolynomial`, lines 44–52 | Same short name under the `Langlands.NYLL` prefix; the product and both explicit arguments are retained. |
| Universes and standing context, lines 27–40 | Preserve four independent levels, both supplied fields, algebra, chosen DVFs, finite dimensionality and extension instance; omit the unused surrounding `IsGalois` variable. |
| `HasUniqueValuationExtension.{u,v,w,x,x}` and `valuationSubringAutOfUniqueExtension` | Reuse their published `Langlands.NYLL` declarations without redefining them. |
| Broad `RealLowerGroups`, `ChevalleyExtension` and polynomial-lifts imports | Replace with published `RealLowerGroups.ValuationSubringAut` and `Mathlib.Algebra.Polynomial.Basic`, sufficient for this data definition. |
| File-wide `noncomputable section` and definition-local `classical` | Mark only this definition `noncomputable` and retain its local `classical`. |

Worker 556 extracted this single definition and authored its explanation.
Other modifications replace the file-level documentation with the focused
scope, clarify the declaration's documentation, combine the nested
namespace commands, and omit the unused valuation namespace and polynomial
scope openings. The product body is unchanged apart from namespace
resolution through the published imports.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author notices are retained: copyright 2026
Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex). The source is Apache-2.0. The existing verbatim
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
The NOTICE has no source-specific entry for this file. No applicable NYLL
entry was found in the workspace's published errata.

This unit defines the polynomial only. Monicity, automorphism invariance,
coefficient descent and the subsequent integral-closure conclusions are
separate work. The approved environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
