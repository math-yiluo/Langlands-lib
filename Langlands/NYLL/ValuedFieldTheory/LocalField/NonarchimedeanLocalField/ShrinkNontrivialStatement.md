# Nontriviality of the transported valuative relation: statement

`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_isNontrivialStatement.{u}`
is the following universal Prop-valued definition, corresponding to source
row M422.005:

```lean
def shrinkLocalField_isNontrivialStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ValuativeRel.IsNontrivial (Shrink.{0} K)
```

## Parameters, local smallness and the relation

The universe `u` is arbitrary. For each carrier `K`, the four supplied
instances occur in exactly this order: `Field K`, `ValuativeRel K`,
`TopologicalSpace K`, and `IsNonarchimedeanLocalField K`. The last instance
certifies the local-field properties for the preceding supplied structures.
There is no additional smallness premise, chosen equivalence, assumed
conclusion or restriction to a canonical relation or topology.

The local `Small.{0} K` instance is the published theorem
`Langlands.NYLL.LocalFieldTheory.nonarchimedeanLocalField_small K`. It
makes Mathlib's actual carrier `Shrink.{0} K : Type 0` available. The
semiring structure on this carrier is Mathlib's transported instance from
`Mathlib.Algebra.Ring.Shrink`, namely `(equivShrink K).symm.semiring`, built
from the supplied field structure on `K`.

The locally installed valuative relation on `Shrink.{0} K` is exactly the
published data
`Langlands.NYLL.LocalFieldTheory.shrinkLocalFieldValuativeRel K`. That
definition applies Mathlib's `ValuativeRel.ofValuation` to the published
`shrinkLocalFieldValuation K`. That valuation is the canonical valuation of
the supplied relation on `K`, pulled back along
`Shrink.ringEquiv K : Shrink.{0} K ≃+* K`. No other relation is used. An
explicit-instance printout of the compiled target shows that the semiring
argument of `ValuativeRel.IsNontrivial` is the same `Shrink.instSemiring`
term as the one in the type of `shrinkLocalFieldValuativeRel K`. Thus the
local installation needs no instance conversion.

The conclusion is Mathlib's class `ValuativeRel.IsNontrivial` for this
installed relation on `Shrink.{0} K`. Its single field states that some
element of `ValuativeRel.ValueGroupWithZero (Shrink.{0} K)` is different
from both `0` and `1`. That value group is formed from the transported
relation on the universe-zero carrier, not from the relation on `K`. The
file introduces no global instance.

The single import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkValuativeRel`.
Its existing dependencies supply the smallness theorem, the published
valuation, Mathlib's transported ring and field structures on `Shrink`, and
Mathlib's `ValuativeRel.IsNontrivial`. They are reused unchanged.

## Statement only

The complete source theorem signature is packaged as this universal `Prop`
target. The definition states the proposition and does not prove it. The
exact proof belongs to a later proof child with the intended name
`Langlands.NYLL.LocalFieldTheory.shrinkLocalField_isNontrivial`. This unit
contains no M422.006–009 property, coherent Artin-family transport or host
assembly.

## Source correspondence and adaptations

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[ShrinkTransport.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkTransport.lean>).
The full source file was read and its SHA-256 checked as
`7d6d13362397f9f4204f6d7b43712fcd1510a53775ae97d479dd9c15876a1e5c`.
Its section parameters are at lines 27–28 and its private smallness wrapper
`smallLocalField` at lines 30–31. The transported relation
`shrinkLocalFieldValuativeRel` is at lines 41–46, including its attribute.
The selected theorem `shrinkLocalField_isNontrivial` has its docstring at
line 55, its signature at lines 56–59 and its proof at lines 59–71.

| Source row and original declaration | Adapted declaration |
| --- | --- |
| M422.005, `LocalFieldTheory.shrinkLocalField_isNontrivial` | `Langlands.NYLL.LocalFieldTheory.shrinkLocalField_isNontrivialStatement` |

The original theorem signature becomes a universal `Prop` definition. It
keeps the original's arbitrary universe and all four section-variable
instances, in order, as explicit universal binders. The source's private
`smallLocalField K` wrapper is replaced by local use of the published
`nonarchimedeanLocalField_small K`, which the wrapper itself returned. The
source relation is replaced by the published adapted relation
`shrinkLocalFieldValuativeRel K`, referenced by name. The two `letI`
installations and the conclusion are otherwise unchanged. The namespace
gains `Langlands.NYLL`, and the statement name gains `Statement`. The
source imports become the one published relation import, and the source's
unused topology import is not needed. The source proof is not copied.
No feasibility draft, reused private adaptation or compatibility patch is
used, and M422 carries no patch10 modification flag.

The registered original collection is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No workspace, project, current Library or pinned-source `notes/errata`
directory was present at preparation.

The Lean header preserves the original 2026 copyright, Apache-2.0
attribution and authorship, including OpenAI Codex assistance, and records
Worker 1803's adaptations. Worker 1803 is the sole author of this
adaptation. The existing [LICENSE](../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../licenses/NYLL/NOTICE) match the pinned
originals byte for byte. Their SHA-256 values are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The root NOTICE has no entry for this source module.
