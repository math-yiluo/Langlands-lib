# NYLL M040.016: finite Galois quotient induction target

This module states the finite Galois quotient induction target. It supplies a
proposition definition; its proof belongs to a separate task.

## Source and name map

The original is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`,
lines 158–166 (M040.016; binders and conclusion at 158–162, proof at 163–165).
The original docstring is at lines 156–157, the ambient group binders at
line 31, the universe at line 27, and the implicit base subgroup at line 46.
The file SHA-256 is
`c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`.
The readable source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| `ClassFormation.FiniteGaloisSubextension.extensionQuotient_inductionOn` | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotient_inductionOnStatement` |

## Complete telescope and meaning

With universe `u`, the definition has the complete telescope

```lean
{G : Type u} [Group G] [TopologicalSpace G]
{K : ClosedSubgroup G}
(L : Langlands.NYLL.ClassFormation.FiniteGaloisSubextension K)
{motive : L.extensionQuotient → Prop}
(q : L.extensionQuotient)
(mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k))
```

It returns `Prop` with body exactly `motive q`. Thus, given a proposition on
the actual named finite Galois quotient and a proof on every canonical
representative, the target is that proposition at `q`. The `mk` hypothesis
remains an explicit dependent binder even though the conclusion does not
mention it. The motive stays implicit and Prop-valued, and the quotient
remains in `Type u`. No `IsTopologicalGroup G` assumption is added.

The imported module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`
supplies the published declarations
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension`,
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotient`
and
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk`.
These preserve the original finite Galois bundle, quotient and projection.
Mathlib's quotient induction underlies the original proof; this module
introduces only its exact source target on those published objects.

## Modification record

Worker 529 made these changes:

1. Prefix `ClassFormation` with `Langlands.NYLL` and replace the original
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient`
   import with the published finite Galois definitions module.
2. Replace `protected theorem extensionQuotient_inductionOn` with
   `protected def extensionQuotient_inductionOnStatement`, retaining the
   `protected` modifier. Move the source conclusion to the definition body,
   add the result annotation `: Prop`, and omit the source proof. All
   parameters, instances, binder kinds, their order and universe are retained.
3. Add `set_option linter.unusedVariables false in` for this declaration,
   because its retained hypothesis `mk` is unused in the proposition body.
4. Replace the original module docstring with the focused target and
   modification description. Prefix the source declaration docstring with
   `Target M040.016:` and adjust capitalization and wrapping.
5. Omit the unused `open KummerTheory`, `open CyclicCohomology`,
   `noncomputable section` and `GroupOnly` section wrapper. This definition
   computes only a proposition and needs none of those commands. Omit all
   other source declarations.

The original copyright and author header is retained. The existing Library
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are retained without modification.
